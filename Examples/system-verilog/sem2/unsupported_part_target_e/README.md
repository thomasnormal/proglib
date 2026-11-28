# Unsupported packed-array part-select target

The parser retains the unsupported `a[3 -: 1]` continuous-assignment target. The source-shaped memory route refuses that process under IEEE 1800-2023 §11.5.1 instead of silently dropping it. The clean-room row records no simulator value claim because the ordinary route must refuse before execution.
