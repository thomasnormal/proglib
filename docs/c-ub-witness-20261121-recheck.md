# C UB witness recheck, 2026-11-21

After commits `bbc0432cc` through `b7fdd6ef9`, the two model UB divergences from the initial audit no longer emit `MemFault` UB verdicts.

| row | sanitizer | model after repair |
| --- | --- | --- |
| `20000113-1.c` | clean | loud `unsupported: no bit-field layout for 'x2'` |
| `bf-sign-2.c` | clean | loud `unsupported: bit-field width 31` |

The six rows rejected by the current structured probe remain frontend refusals. The required audit therefore has zero clean-sanitizer UB verdicts in the current runner, with the two unsupported rows still requiring a future parser/layout widening step.
