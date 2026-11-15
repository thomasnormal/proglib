# Module constant function in canonical E

This clean-room source retains an automatic input-only module function as a
parser-shaped `Function` declaration and evaluates its call while binding a
parameter-dependent `localparam` in canonical E. The loader carries the
function declarations into parameter and localparam binding before evaluating
packed dimensions (IEEE 1800-2023 §§10.8, 13.4).

The three `N=1,8,16` rows match Icarus Verilog 13.0 and Xcelium
24.03-s004; run `python3 check.py` for the differential receipt.
