# RV32UI battery inventory

This manifest pins the upstream `riscv-tests` `isa/rv32ui` source-program set used for the D battery. The pinned `ld_st.S`, `addi.S`, `beq.S`, `and.S`, `sub.S`, `jal.S`, and `lui.S` images are the seven compiled-and-run programs. The remaining 35 source programs still lack a reset/memory image build in this battery.
