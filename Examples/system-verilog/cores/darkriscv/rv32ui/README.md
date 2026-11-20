# RV32UI battery inventory

This manifest pins the upstream `riscv-tests` `isa/rv32ui` source-program set used for the D battery. The current host has no RISC-V cross assembler or linker configuration for the repository's reset/memory testbench, so the compiled-and-run count is `0/42`. The source inventory is retained to make that missing build stage explicit. No simulator or Lean result is claimed for these source files.
