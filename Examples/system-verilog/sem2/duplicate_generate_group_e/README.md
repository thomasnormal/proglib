# Duplicate active generate scope

The source has two active generate arrays using the same scope name `g`, the
clean-room `blk_duplicate_generate_group` shape. The approved extractor
retains both parser nodes. Ordinary E refuses the duplicate active names
loudly, while Icarus Verilog 13.0 and Xcelium 24.03-s004 agree on four source
rows. The receipt command is `python3 Examples/system-verilog/sem2/duplicate_generate_group_e/check.py`.
