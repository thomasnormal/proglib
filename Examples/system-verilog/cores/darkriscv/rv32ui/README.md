# DarkRISCV RV32UI differential

Icarus Verilog 13.0 (`s20250103-64-gdad78d525`), Xcelium 24.03-s004 and
canonical E agree on **42/42 images and 25,501/25,501 cycles**. The checker
builds every assembly file in the pinned upstream `isa/rv32ui` directory and
compares that inventory to `programs.txt`. The ten earlier 300-cycle traces
use a different memory environment and are counted separately.

| Observation on the unmodified core | Images |
| --- | ---: |
| Reached the upstream pass sequence, then issued `ecall` | 41 |
| Issued `ecall` there with the expected `gp=1, a0=0, a7=93` | 0 |
| Re-entered the reset vector before reaching a pass or fail label | 1 (`fence_i.S`) |

For all 41 pass sequences, the execute stage sees the leading `fence`
(`0x0ff0000f`) with `IERR=1`. The next two instructions, which set `gp` and
`a7`, are flushed. At `ecall`, `a0=0` and `a7=0`. In `fence_i.S`, the core
raises `IERR` on `fence.i` at PC `0x1d0` and executes the reset vector a
second time at cycle 160. Each run ends at the first executing `ecall` or
second visit to the reset vector. Execution after that boundary is unmeasured.

The instruction port returns the fetched word on the following clock, as in
the upstream Harvard instruction RAM. The data port reads the aligned word and
applies acknowledged stores to the selected byte lanes. Instruction and data
acknowledgements introduce deterministic wait states. The ELF image includes
linked data at its actual address. In `ld_st.S`, all test numbers 2 through
49 execute and the core reaches the pass label at cycle 1579. The load/store
image has 527 cycles waiting for instruction acknowledgement and 112 waiting
for data acknowledgement.

## Reproduction

Use the `riscv-tests` checkout at `3df703cd52d5f0d8224e3c50bf03c6cb70efff98`
with its `env` submodule at `6de71edb142be36319e380ce782c3d1830c65d68`.
The image builder uses Clang and LLD 21.1.8, GNU objcopy and nm. From the
repository root, run the following with the checkout path as the argument.

```sh
python3 Examples/system-verilog/cores/darkriscv/rv32ui/memory_check.py "$RISCV_TESTS"
```

Optional trailing program names select a subset, for example `ld_st.S lb.S`.
Both simulators run the bundled DarkRISCV with `SIMULATION` defined. The
checker compares their live rows against each other and the saved transcript,
then replays the input fields through `dark.e 0` and `fastStepCanonical`.
Each row samples the rising edge before nonblocking assignments commit. E
compares the state after applying that edge's input values and before raising
the clock. The comparison includes four reset clocks per image, all twelve output ports,
the execute PC and word, pipeline controls, `IERR`, and registers `gp/a0/a7`.
One control changes a sampled `IDREQ` bit and must fail the E comparison.
Another changes the first `lb.S` test byte from `0xff` to `0xfe` in a
temporary memory image and must reach the upstream fail label on the three
engines.

Each `BEGIN` line in the gzip transcript identifies the program, complete
image SHA-256 and terminal observation. `ROW` lines give the cycle number and
sampled signals in the order of `COLUMNS` in the checker. Four-state values
are binary, MSB first. [Transcript](memory_rows.txt.gz) · [Checker](memory_check.py) · [Upstream tests](https://github.com/riscv-software-src/riscv-tests/tree/3df703cd52d5f0d8224e3c50bf03c6cb70efff98/isa/rv32ui)
