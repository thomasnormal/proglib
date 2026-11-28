# Signed packed-array target refusal

This clean-room row covers signed and unsigned packed-array element targets. The source-shaped memory route refuses the packed-array target when its scalar target lowering is outside the admitted fragment, preserving the unsupported boundary instead of returning an all-x trace. IEEE 1800-2023 §11.5.1 remains the governing select-target rule.
