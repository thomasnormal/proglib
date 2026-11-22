# RV32UI battery inventory

This manifest pins the upstream `riscv-tests` `isa/rv32ui` source-program set used for the D battery. The pinned `ld_st.S`, `addi.S`, `beq.S`, `and.S`, `sub.S`, `jal.S`, `lui.S`, `or.S`, `xor.S`, and `xori.S` images are the ten compiled-and-run programs. The remaining 32 source programs still lack a reset/memory image build in this battery.
