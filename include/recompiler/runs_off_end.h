#ifndef __RECOMPILER_RUNS_OFF_END_H__
#define __RECOMPILER_RUNS_OFF_END_H__

#include <cstddef>
#include <cstdint>

namespace N64Recomp {
    // [wcw fullconv] Whether a function's last words let control run off its end. `last` is its last instruction word,
    // `prev` the one before when there is one; `last_word_is_label`: a branch lands on the last word, which runs on
    // even after a jump (aki-roadmap#76). Those that do continue at the next address through the lookup. A one-word
    // function counts too: a hack's hook can return just before a stock function start (aki-roadmap#173: House Party
    // Mixtape's entry 0x8001E340 before func_8001E344 fell off the generated code into whatever came next).
    inline bool function_runs_off_end(size_t word_count, uint32_t last, uint32_t prev, bool last_word_is_label) {
        auto ends_flow = [](uint32_t w) {
            uint32_t op = w >> 26;
            if (op == 0x02) return true;                                    // j
            if (op == 0x00 && (w & 0x3F) == 0x08) return true;              // jr
            if (op == 0x04 && ((w >> 16) & 0x3FF) == 0) return true;        // b (beq zero, zero)
            return false;
        };
        if (word_count == 0 || ends_flow(last) || last == 0x42000018) {     // not eret either
            return false;
        }
        return word_count == 1 || last_word_is_label || !ends_flow(prev);
    }
}

#endif
