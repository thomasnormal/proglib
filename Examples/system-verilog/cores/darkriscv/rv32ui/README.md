# RV32UI battery inventory

This manifest pins the upstream `riscv-tests` `isa/rv32ui` source-program set used for the D battery. The pinned `ld_st.S`, `addi.S`, and `beq.S` images are the three compiled-and-run programs. The remaining 39 source programs still lack a reset/memory image build in this battery.
