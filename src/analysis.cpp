#include <set>
#include <algorithm>

#include "rabbitizer.hpp"
#include "fmt/format.h"

#include "recompiler/context.h"
#include "analysis.h"

extern "C" const char* RabbitizerRegister_getNameGpr(uint8_t regValue);

// If 64-bit addressing is ever implemented, these will need to be changed to 64-bit values
struct RegState {
    // For tracking a register that will be used to load from RAM
    uint32_t prev_lui;
    uint32_t prev_addiu_vram;
    uint32_t prev_addu_vram;
    uint8_t prev_addend_reg;
    uint32_t prev_got_offset; // offset of lw rt,offset(gp)
    bool valid_lui;
    bool valid_addiu;
    bool valid_addend;
    bool valid_got_offset;
    // For tracking a register that has been loaded from RAM
    uint32_t loaded_lw_vram;
    uint32_t loaded_addu_vram;
    uint32_t loaded_address;
    uint8_t loaded_addend_reg;
    bool valid_loaded;
    bool valid_got_loaded; // valid load through the GOT

    RegState() = default;

    void invalidate() {
        prev_lui = 0;
        prev_addiu_vram = 0;
        prev_addu_vram = 0;
        prev_addend_reg = 0;
        prev_got_offset = 0;

        valid_lui = false;
        valid_addiu = false;
        valid_addend = false;
        valid_got_offset = false;

        loaded_lw_vram = 0;
        loaded_addu_vram = 0;
        loaded_address = 0;
        loaded_addend_reg = 0;

        valid_loaded = false;
        valid_got_loaded = false;
    }
};

using InstrId = rabbitizer::InstrId::UniqueId;
using RegId = rabbitizer::Registers::Cpu::GprO32;

bool analyze_instruction(const rabbitizer::InstructionCpu& instr, const N64Recomp::Function& func, N64Recomp::FunctionStats& stats,
    RegState reg_states[32], std::vector<RegState>& stack_states, bool is_got_addr_defined) {
    // Temporary register state for tracking the register being operated on
    RegState temp{};

    int rd = (int)instr.GetO32_rd();
    int rs = (int)instr.GetO32_rs();
    int base = rs;
    int rt = (int)instr.GetO32_rt();
    int sa = (int)instr.Get_sa();

    uint16_t imm = instr.Get_immediate();

    auto check_move = [&]() {
        if (rs == 0) {
            // rs is zero so copy rt to rd
            reg_states[rd] = reg_states[rt];
        } else if (rt == 0) {
            // rt is zero so copy rs to rd
            reg_states[rd] = reg_states[rs];
        } else {
            // Not a move, invalidate rd
            reg_states[rd].invalidate();
        }
    };

    switch (instr.getUniqueId()) {
    case InstrId::cpu_lui:
        // rt has been completely overwritten, so invalidate it
        reg_states[rt].invalidate();
        reg_states[rt].prev_lui = (int16_t)imm << 16;
        reg_states[rt].valid_lui = true;
        break;
    case InstrId::cpu_addiu:
        // The target reg is a copy of the source reg plus an immediate, so copy the source reg's state
        reg_states[rt] = reg_states[rs];
        // Set the addiu state if and only if there hasn't been an addiu already
        if (!reg_states[rt].valid_addiu) {
            reg_states[rt].prev_addiu_vram = (int16_t)imm;
            reg_states[rt].valid_addiu = true;
        } else {
            // Otherwise, there have been 2 or more consecutive addius so invalidate the whole register
            reg_states[rt].invalidate();
        }
        break;
    case InstrId::cpu_addu:
        // rd has been completely overwritten, so invalidate it
        temp.invalidate();
        if (reg_states[rs].valid_got_offset != reg_states[rt].valid_got_offset) {
            // Track which of the two registers has the valid GOT offset state and which is the addend
            int valid_got_offset_reg = reg_states[rs].valid_got_offset ? rs : rt;
            int addend_reg = reg_states[rs].valid_got_offset ? rt : rs;

            // Copy the got offset reg's state into the destination reg, then set the destination reg's addend to the other operand
            temp = reg_states[valid_got_offset_reg];
            temp.valid_addend = true;
            temp.prev_addend_reg = addend_reg;
            temp.prev_addu_vram = instr.getVram();
        } else if (((rs == (int)RegId::GPR_O32_gp) || (rt == (int)RegId::GPR_O32_gp)) 
                && reg_states[rs].valid_got_loaded != reg_states[rt].valid_got_loaded) {
            // `addu rd, rs, $gp` or `addu rd, $gp, rt` after valid GOT load, this is the last part of a position independent
            // jump table call. Keep the register state intact.
            int valid_got_loaded_reg = reg_states[rs].valid_got_loaded ? rs : rt;

            temp = reg_states[valid_got_loaded_reg];
        }
        // Exactly one of the two addend register states should have a valid lui at this time
        else if (reg_states[rs].valid_lui != reg_states[rt].valid_lui) {
            // Track which of the two registers has the valid lui state and which is the addend
            int valid_lui_reg = reg_states[rs].valid_lui ? rs : rt;
            int addend_reg = reg_states[rs].valid_lui ? rt : rs;

            // Copy the lui reg's state into the destination reg, then set the destination reg's addend to the other operand
            temp = reg_states[valid_lui_reg];
            temp.valid_addend = true;
            temp.prev_addend_reg = addend_reg;
            temp.prev_addu_vram = instr.getVram();
        } else {
            // Check if this is a move
            check_move();
        }
        reg_states[rd] = temp;
        break;
    case InstrId::cpu_daddu:
    case InstrId::cpu_or:
        check_move();
        break;
    case InstrId::cpu_sw:
        // If this is a store to the stack, copy the state of rt into the stack at the given offset
        if (base == (int)RegId::GPR_O32_sp) {
            if ((imm & 0b11) != 0) {
                fmt::print(stderr, "Invalid alignment on offset for sw to stack: {}\n", (int16_t)imm);
                return false;
            }
            if (((int16_t)imm) < 0) {
                fmt::print(stderr, "Negative offset for sw to stack: {}\n", (int16_t)imm);
                return false;
            }
            size_t stack_offset = imm / 4;
            if (stack_offset >= stack_states.size()) {
                stack_states.resize(stack_offset + 1);
            }
            stack_states[stack_offset] = reg_states[rt];
        }
        break;
    case InstrId::cpu_lw:
        // rt has been completely overwritten, so invalidate it
        temp.invalidate();
        // If this is a load from the stack, copy the state of the stack at the given offset to rt
        if (base == (int)RegId::GPR_O32_sp) {
            if ((imm & 0b11) != 0) {
                fmt::print(stderr, "Invalid alignment on offset for lw from stack: {}\n", (int16_t)imm);
                return false;
            }
            if (((int16_t)imm) < 0) {
                fmt::print(stderr, "Negative offset for lw from stack: {}\n", (int16_t)imm);
                return false;
            }
            size_t stack_offset = imm / 4;
            if (stack_offset >= stack_states.size()) {
                stack_states.resize(stack_offset + 1);
            }
            temp = stack_states[stack_offset];
        }
        // If the base register has a valid lui state and a valid addend before this, then this may be a load from a jump table
        else if (reg_states[base].valid_lui && reg_states[base].valid_addend) {
            // Exactly one of the lw and the base reg should have a valid lo16 value. However, the lo16 may end up just being zero by pure luck,
            // so allow the case where the lo16 immediate is zero and the register state doesn't have a valid addiu immediate.
            // This means the only invalid case is where they're both true.
            bool nonzero_immediate = imm != 0;
            if (!(nonzero_immediate && reg_states[base].valid_addiu)) {
                uint32_t lo16;
                if (nonzero_immediate) {
                    lo16 = (int16_t)imm;
                } else {
                    lo16 = reg_states[base].prev_addiu_vram;
                }

                uint32_t address = reg_states[base].prev_lui + lo16;
                temp.valid_loaded = true;
                temp.loaded_lw_vram = instr.getVram();
                temp.loaded_address = address;
                temp.loaded_addend_reg = reg_states[base].prev_addend_reg;
                temp.loaded_addu_vram = reg_states[base].prev_addu_vram;
            }
        }
        // If the base register has a valid GOT offset and a valid addend before this, then this may be a load from a position independent jump table
        else if (reg_states[base].valid_got_offset && reg_states[base].valid_addend) {
            // At this point, we will have the offset from the value of the previously read GOT entry to the address being
            // loaded here as well as the GOT entry offset itself
            temp.valid_got_loaded = true;
            temp.loaded_lw_vram = instr.getVram();
            temp.loaded_address = imm; // This address is relative for now, we'll calculate the absolute address later
            temp.loaded_addend_reg = reg_states[base].prev_addend_reg;
            temp.loaded_addu_vram = reg_states[base].prev_addu_vram;
            temp.prev_got_offset = reg_states[base].prev_got_offset;
        } else if (base == (int)RegId::GPR_O32_gp && is_got_addr_defined) {
            // lw from the $gp register implies a read from the global offset table
            temp.prev_got_offset = imm;
            temp.valid_got_offset = true;
        }
        reg_states[rt] = temp;
        break;
    case InstrId::cpu_jr:
        // Ignore jr $ra
        if (rs == (int)rabbitizer::Registers::Cpu::GprO32::GPR_O32_ra) {
            break;
        }
        // Check if the source reg has a valid loaded state and if so record that as a jump table
        if (reg_states[rs].valid_loaded) {
            stats.jump_tables.emplace_back(
                reg_states[rs].loaded_address,
                reg_states[rs].loaded_addend_reg,
                0,
                reg_states[rs].loaded_lw_vram,
                reg_states[rs].loaded_addu_vram,
                instr.getVram(),
                0, // section index gets filled in later
                std::nullopt,
                std::vector<uint32_t>{}
            );
        } else if (reg_states[rs].valid_got_loaded) {
            stats.jump_tables.emplace_back(
                reg_states[rs].loaded_address,
                reg_states[rs].loaded_addend_reg,
                0,
                reg_states[rs].loaded_lw_vram,
                reg_states[rs].loaded_addu_vram,
                instr.getVram(),
                0, // section index gets filled in later
                reg_states[rs].prev_got_offset,
                std::vector<uint32_t>{}
            );
        }
        // TODO stricter validation on tail calls, since not all indirect jumps can be treated as one.
        break;
    default:
        if (instr.modifiesRd()) {
            reg_states[rd].invalidate();
        }
        if (instr.modifiesRt()) {
            reg_states[rt].invalidate();
        }
        break;
    }
    return true;
}

// [wcw fullconv] The case count a switch's own bounds check allows: `sltiu rT, rI, N` before the
// `sll addend, rI, 2` that scales the index added to the table address. Searched backwards from that addu, a few
// instructions at most (the compiler keeps them together); nullopt when the pattern isn't there or a register in it is
// written in between.
static std::optional<uint32_t> find_jump_table_bound(const N64Recomp::Function& func, const N64Recomp::JumpTable& jtbl) {
    constexpr uint32_t max_back = 16;
    if (jtbl.addu_vram < func.vram) {
        return std::nullopt;
    }
    const size_t addu_index = (jtbl.addu_vram - func.vram) / sizeof(uint32_t);
    if (addu_index >= func.words.size()) {
        return std::nullopt;
    }
    auto op = [](uint32_t w) { return w >> 26; };
    auto rs = [](uint32_t w) { return (w >> 21) & 31; };
    auto rt = [](uint32_t w) { return (w >> 16) & 31; };
    auto rd = [](uint32_t w) { return (w >> 11) & 31; };
    auto sa = [](uint32_t w) { return (w >> 6) & 31; };
    auto funct = [](uint32_t w) { return w & 0x3F; };
    // the GPR an instruction writes, if any (enough to see a register reused between the guard and the addu)
    auto written = [&](uint32_t w) -> uint32_t {
        const uint32_t o = op(w);
        if (o == 0) {
            const uint32_t f = funct(w);
            return (f == 0x08 || f == 0x0C || f == 0x0D || f == 0x0F || (f >= 0x18 && f <= 0x1F) || f == 0x11 || f == 0x13) ? 0 : rd(w);
        }
        if (o == 0x03) {
            return 31;
        }
        return ((o >= 0x08 && o <= 0x0F) || (o >= 0x18 && o <= 0x1B) || (o >= 0x20 && o <= 0x27) || o == 0x37) ? rt(w) : 0;
    };
    for (size_t i = addu_index; i-- > 0 && addu_index - i <= max_back;) {
        const uint32_t w = func.words[i];
        if (written(w) != jtbl.addend_reg) {
            continue;
        }
        if (!(op(w) == 0 && funct(w) == 0 && sa(w) == 2 && rt(w) != 0)) {
            return std::nullopt;
        }
        const uint32_t index_reg = rt(w);
        for (size_t j = i; j-- > 0 && i - j <= max_back;) {
            const uint32_t v = func.words[j];
            if (op(v) == 0x0B && rs(v) == index_reg) {
                const uint32_t bound = v & 0xFFFF;
                if (bound == 0 || bound > 0x1000) {
                    return std::nullopt;
                }
                return bound;
            }
            if (written(v) == index_reg) {
                return std::nullopt;
            }
        }
        return std::nullopt;
    }
    return std::nullopt;
}

bool N64Recomp::analyze_function(const N64Recomp::Context& context, const N64Recomp::Function& func,
    const std::vector<rabbitizer::InstructionCpu>& instructions, N64Recomp::FunctionStats& stats) {
    const Section* section = &context.sections[func.section_index];
    std::optional<uint32_t> got_ram_addr = section->got_ram_addr;

    // Create a state to track each register (r0 won't be used)
    RegState reg_states[32] {};
    std::vector<RegState> stack_states{};

    // Look for jump tables
    // A linear search through the func won't be accurate due to not taking control flow into account, but it'll work for finding jtables
    for (const auto& instr : instructions) {
        if (!analyze_instruction(instr, func, stats, reg_states, stack_states, got_ram_addr.has_value())) {
            return false;
        }
    }

    // Calculate absolute addresses for position-independent jump tables
    if (got_ram_addr.has_value()) {
        uint32_t got_rom_addr = got_ram_addr.value() + func.rom - func.vram;

        for (size_t i = 0; i < stats.jump_tables.size(); i++) {
            JumpTable& cur_jtbl = stats.jump_tables[i];

            if (cur_jtbl.got_offset.has_value()) {
                uint32_t got_word = byteswap(*reinterpret_cast<const uint32_t*>(&context.rom[got_rom_addr + cur_jtbl.got_offset.value()]));

                cur_jtbl.vram += (section->ram_addr + got_word);
            }
        }
    }

    // Sort jump tables by their address
    std::sort(stats.jump_tables.begin(), stats.jump_tables.end(),
        [](const JumpTable& a, const JumpTable& b)
    {
        return a.vram < b.vram;
    });

    // Determine jump table sizes
    for (size_t i = 0; i < stats.jump_tables.size(); i++) {
        JumpTable& cur_jtbl = stats.jump_tables[i];
        uint32_t end_address = (uint32_t)-1;
        uint32_t entry_count = 0;
        uint32_t vram = cur_jtbl.vram;

        if (i < stats.jump_tables.size() - 1) {
            end_address = stats.jump_tables[i + 1].vram;
        }

        // TODO this assumes that the jump table is in the same section as the function itself
        // [wcw fullconv] ...unless Context::jump_table_data_ranges says where it is.
        auto jtbl_rom_of = [&context, &func](uint32_t addr) -> uint32_t {
            for (const auto& range : context.jump_table_data_ranges) {
                if (addr >= range[0] && addr < range[1]) {
                    return range[2] + (addr - range[0]);
                }
            }
            return addr + func.rom - func.vram;
        };
        cur_jtbl.rom = jtbl_rom_of(cur_jtbl.vram);
        cur_jtbl.section_index = func.section_index;

        // [wcw fullconv] With unknown jumps as lookup tail calls, a table whose bounds check is known holds at least
        // that many cases, wherever they point: a hack can redirect a case into another function's body
        // (VPW64 Deluxe, aki-roadmap#123: a case into the middle of another function of the overlay). Ending the
        // table at such a case cut off the cases after it, and the game reaching one aborted with a switch error.
        // Entries the scan below accepts anyway still extend the table past the bound, as before, so a guard matched
        // wrongly never makes a table smaller.
        std::optional<uint32_t> bound{};
        if (context.tail_call_unknown_jumps_by_lookup) {
            bound = find_jump_table_bound(func, cur_jtbl);
        }

        while (vram < end_address) {
            // Retrieve the current entry of the jump table
            // TODO same as above
            uint32_t rom_addr = jtbl_rom_of(vram);
            // [wcw fullconv] Stop at the end of the ROM instead of reading past it.
            if ((size_t)rom_addr + sizeof(uint32_t) > context.rom.size()) {
                break;
            }
            uint32_t jtbl_word = byteswap(*reinterpret_cast<const uint32_t*>(&context.rom[rom_addr]));

            if (cur_jtbl.got_offset.has_value() && got_ram_addr.has_value()) {
                // Position independent jump tables have values that are offsets from the GOT,
                // convert those to absolute addresses
                jtbl_word += got_ram_addr.value();
            }

            // Check if the entry is a valid address in the current function
            if (jtbl_word < func.vram || jtbl_word >= func.vram + func.words.size() * sizeof(func.words[0])) {
                // [wcw fullconv] ...or in code a hack added (a case redirected there).
                bool external = false;
                for (const auto& [ext_start, ext_end] : context.external_code_ranges) {
                    if (jtbl_word >= ext_start && jtbl_word < ext_end) {
                        external = true;
                        break;
                    }
                }
                // ...or, when unknown jumps are lookup tail calls, in a section whose data the table
                // was read from (hack code dispatching through an overlay's own switch table).
                if (!external && context.tail_call_unknown_jumps_by_lookup) {
                    for (const auto& range : context.jump_table_data_ranges) {
                        if (jtbl_word >= range[0] && jtbl_word < range[1]) {
                            external = true;
                            break;
                        }
                    }
                }
                // If it's not then this is the end of the jump table
                if (!external && (!bound.has_value() || cur_jtbl.entries.size() >= bound.value())) {
                    break;
                }
            }
            cur_jtbl.entries.push_back(jtbl_word);
            vram += 4;
        }

        if (cur_jtbl.entries.size() == 0) {
            fmt::print("Failed to determine size of jump table at 0x{:08X} for instruction at 0x{:08X}\n", cur_jtbl.vram, cur_jtbl.jr_vram);
            return false;
        }

        //fmt::print("Jtbl at 0x{:08X} (rom 0x{:08X}) with {} entries used by instr at 0x{:08X}\n", cur_jtbl.vram, cur_jtbl.rom, cur_jtbl.entries.size(), cur_jtbl.jr_vram);
    }

    // [wcw fullconv] A table whose cases all lie outside the function (hack code dispatching through an
    // overlay's own switch table) is no switch of this function: with unknown jumps as lookup tail calls,
    // leave the load alone and let the jr be an indirect tail call through the lookup.
    if (context.tail_call_unknown_jumps_by_lookup) {
        uint32_t func_end = func.vram + (uint32_t)(func.words.size() * sizeof(func.words[0]));
        std::erase_if(stats.jump_tables, [&](const JumpTable& jtbl) {
            return std::all_of(jtbl.entries.begin(), jtbl.entries.end(),
                [&](uint32_t e) { return e < func.vram || e >= func_end; });
        });
    }

    return true;
}
