#ifndef __RECOMPILER_JUMP_TABLE_BOUND_H__
#define __RECOMPILER_JUMP_TABLE_BOUND_H__

#include <cstddef>
#include <cstdint>
#include <optional>

namespace N64Recomp {
    // [wcw fullconv] The case count a switch's own bounds check allows: `sltiu rT, rI, N` before the
    // `sll addend, rI, 2` that scales the index added to the table address. Searched backwards from that addu, a few
    // instructions at most (the compiler keeps them together); nullopt when the pattern isn't there or a register in it is
    // written in between.
    // `rom_words` holds the function as Function::words does: in ROM byte order on a little-endian host, which is why
    // every word is swapped here (aki-roadmap#206: reading them unswapped never found a bound).
    inline std::optional<uint32_t> find_jump_table_bound(const uint32_t* rom_words, size_t word_count, size_t addu_index, uint32_t addend_reg) {
        constexpr uint32_t max_back = 16;
        if (addu_index >= word_count) {
            return std::nullopt;
        }
        auto word_at = [rom_words](size_t index) {
            const uint32_t w = rom_words[index];
            return (w >> 24) | ((w >> 8) & 0xFF00) | ((w << 8) & 0xFF0000) | (w << 24);
        };
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
            const uint32_t w = word_at(i);
            if (written(w) != addend_reg) {
                continue;
            }
            if (!(op(w) == 0 && funct(w) == 0 && sa(w) == 2 && rt(w) != 0)) {
                return std::nullopt;
            }
            const uint32_t index_reg = rt(w);
            for (size_t j = i; j-- > 0 && i - j <= max_back;) {
                const uint32_t v = word_at(j);
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
}

#endif
