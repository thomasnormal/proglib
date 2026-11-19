# R2 core scouting

This is the R2 admission census for three real RISC-V cores.  The source trees
were cloned at the pins below and were not modified.  The extractor and
`load_design_sv2` were run from this repository with Lean 4.33.0-rc1.  The
envelopes were kept outside the repository; their SHA-256 values make the
measurements reproducible without vendoring third-party RTL.

## Pins and licenses

| core | upstream pin | license | top | source files in envelope |
| --- | --- | --- | --- | ---: |
| CV32E40P | [`openhwgroup/cv32e40p`](https://github.com/openhwgroup/cv32e40p), tag `v1.0.1`, `6148cf567f2450052458c21c5b3cc2a02423c69d` | Solderpad Hardware License 0.51 (`LICENSE`) | `riscv_core` | 31 |
| Ibex | [`lowRISC/ibex`](https://github.com/lowRISC/ibex), `master`, `d513671dae09e701ceb6cd732d2da5fb52c13856` | Apache-2.0 (`LICENSE`) | `ibex_top` | 224 |
| PicoRV32 | [`YosysHQ/picorv32`](https://github.com/YosysHQ/picorv32), `main`, `ef203c2b0a3fb793280f5114941416c425c5b461` | ISC (`COPYING`) | `picorv32` | 1 |

The CV32E40P input is every `rtl/*.sv`.  The Ibex input is `rtl/*.sv` plus
the primitive and common-cell SystemVerilog dependency directories selected
by `ibex_top.core` (the broad set keeps unresolved primitive dependencies
visible).  PicoRV32 uses the single `picorv32.v` source from its default
FuseSoC target.  No RTL adaptation was made.

## Commands and measurements

For each clone, the command was the symbolic extractor invocation below, with
the listed source set passed as the final arguments:

```text
python3 extractors/sv/extract.py --top TOP -o RESULT.sv.json SOURCE...
```

The loader probe was a small Lean file containing:

```lean
import LeanModels.Sv.Ingest2
load_design_sv2 NAME from "RESULT.sv.json"
#check NAME
```

| core | extraction wall | envelope bytes / SHA-256 | hierarchy modules | static `Unsupported` nodes | loader result |
| --- | ---: | --- | ---: | ---: | --- |
| CV32E40P | 17.08 s | 21,289,394 / `e588884691159820eac0a28eff5315e721b99fdf989f6611540931e5f264a6de` | 23 | 293 | **refused** |
| Ibex | 39.13 s | 13,914,127 / `ae014736a66a58b0f725d0bf358ee8ebab6fb05ef75e0645ea1507137ce2f7d4` | 20 | 396 | **refused** |
| PicoRV32 | 4.37 s | 3,178,052 / `009cc39591b3fcb1c88403ca44f822cb1854d2ebc0b5c728c7cade06a2e47b1b` | 1 | 70 | **loaded** |

The loader diagnostics below are the complete first errors, copied from the
Lean probes:

```text
CV32E40P:
envelope: module: AlwaysPosedge: AlwaysPosedge:edge — edge-qualified clock requires its retained event semantics

Ibex:
envelope: module: AlwaysLatch: unknown process kind "AlwaysLatch"
```

PicoRV32 loads as a 26-`Nat` parameter family.  Loading is not a claim that
the semantic tier is admitted: at the default values,

```text
(picorv32.sem defaults).hasUnsupported = true
processes.size = 1
[(Instantiate, decl 'cpuregs': unpacked array storage outside E (UnpackedDecl:memory))]
```

Thus its first semantic wall is the register-file unpacked memory, while the
envelope loader itself succeeds.  Its most frequent static walls are
unsized/XZ parametric literals (16), call expressions (13), width
conversions (11), net-z (8), and assignment targets (6); these counts are
telemetry, not silently admitted semantics.

The first admission pass recorded a 2.21-second, 3,181,105-byte envelope with SHA-256
`25ac7e444bd6f4171348484fcba4d99e9c5192036764dabb8b64a6ef8c77be26` before the
extractor was re-run for the current re-probe.  The canonical measurement for
the pinned source is now the reproducible 3,178,052-byte envelope above
(`009cc395…`); the source commit and all loader diagnostics are unchanged.
Later R2 decisions use the canonical envelope, rather than mixing the two
extractor snapshots.

## Ranking and next requests

Measured distance to an R2 proof target is:

1. **PicoRV32** — closest: one-module load succeeds and the remaining first
   semantic wall is a concrete unpacked memory shape (`cpuregs`).
2. **CV32E40P** — next: 23 modules extract, but the loader stops at retained
   edge-process semantics (`AlwaysPosedge`).
3. **Ibex** — last for this tier: the broad dependency closure extracts 20
   modules, but `AlwaysLatch` is encountered before a design family can load;
   primitive/dependency unsupported nodes add further work after that wall.

The result is a scouting decision, not a core selection for the proof rung:
PicoRV32 is the first candidate to revisit after the remaining unpacked-memory
and module-member boundaries land in the SV tier.  No core was rewritten to
fit the loader.

## Current PicoRV32 re-probe

The table above is the original cross-core census.  On 2026-11-07, after the
generic memory route admitted generated members, the pinned PicoRV32 source was
re-extracted with the current extractor and loaded against `github/master`
revision `83638b50fccf1dfe7980f2ca1ab49e1366f34ef4`:

```text
source commit: ef203c2b0a3fb793280f5114941416c425c5b461
envelope: 2d2d3c1b5cdd459b61a29ab38e6384db20f1f4a6cdbf5b211fe47cc2a1e785c8
size: 2,986,551 bytes
```

The declaration still loads as a 26-parameter family.  Its ordinary semantic
family still first refuses at `picorv32.v:203`:

```text
unsupported "Instantiate"
  "decl 'cpuregs': unpacked array storage outside E (UnpackedDecl:memory)"
```

The rebuilt memory route now expands the source-shaped generated members; its
first PicoRV32 refusal is instead the top-level unsupported-member gate:

```text
unsupported "Instantiate"
  "memory cycle route does not yet admit unsupported module members"
```

The first retained member is `NetSymbol:net-z` for `pcpi_mul_wr`, the `wire`
at `picorv32.v:257`.  This is an existing generic net-z boundary.  The
symbolic R2 invariant therefore remains parked at the unpacked `cpuregs` and
net-z/unsupported-member walls; no core-specific adaptation or finite-window
extension was made.

## Latest PicoRV32 re-probe after dynamic parameterized-memory admission

After `github/master` advanced to `cb99d49c69db72421ab3c7b16447b47311f60890`
(`[ls-sv] admit dynamic parameterized register memories`), the unchanged
PicoRV32 source was extracted again.  The fresh envelope is
`bbdf7aee9e200a35f228adfa891eeaa10addb3b1608f3776f0bd9d61c42d4f9c` and
2,992,406 bytes.  The declaration still loads as a 26-parameter family.  The
ordinary semantic family still first refuses the unpacked `cpuregs` memory at
`picorv32.v:203`:

```text
unsupported "Instantiate"
  "decl 'cpuregs': unpacked array storage outside E (UnpackedDecl:memory)"
```

The memory route reaches its existing unsupported-module-member gate before
the new dynamic-memory path can run:

```text
unsupported "Instantiate"
  "memory cycle route does not yet admit unsupported module members"
```

The first retained member is still `NetSymbol:net-z` for `pcpi_mul_wr` at
`picorv32.v:257`, an already catalogued generic boundary.  No new owner-lane
request or core adaptation is justified by this probe.

The owned refinement layer now has a symbolic ADDI-program certificate in
`LeanModels.Refine.RvfiAddiProgram`: arbitrary decoded ADDI lists, arbitrary
invalid RVFI bubbles, and indexed `Rv32iBoundary` witnesses normalize to the
exact stateful ISA trace.  This advances the reusable invariant surface while
the real PicoRV32 instantiation remains blocked by the existing loader walls.
The input-aware `AddiRvfiCycleTrace` extension also retains actual cycle-step
equalities and proves that the adapter's `retireInputs` are exactly the
symbolic ADDI inputs before applying the same trace theorem.
The companion `LeanModels.Refine.RvfiAluProgram` certificate lifts this
surface to arbitrary decoded RV32I ALU instructions, including register,
immediate, pc-based, and upper-immediate operand shapes.
Its `AluRvfiCycleTrace` extension retains actual cycle-step equalities and
retiring inputs, then normalizes the machine's own cycle stream to the same
stateful ALU trace.
`AluRvfiTrace.append` composes raw observation certificates at the next
retirement order and folded architectural state, preserving arbitrary bubble
prefixes while concatenating ALU programs.  The machine-aware
`AluRvfiCycleTrace.append` composes two such certificates at the exact
`rvfiStateAfter`/`aluProgramState` boundary: the second segment starts at the
first segment's next retirement order and receives its threaded core and
architectural states.  The corresponding ALU input, state, and retirement
fold append laws expose the same join for a segmented loaded-core proof.
The stateful-machine bridges `rvMemoryMachineWith_alu_program_state_append`
and `rvMemoryMachineWith_alu_program_trace_append` expose the corresponding
`machineStateAfter` and retirement-trace splits directly, with the first
segment's threaded state feeding the second.

`LeanModels.Refine.RvfiMemProgram` starts the corresponding memory-program
surface.  `MemInstruction` retains a generic RV32I load/store operation and
decoder proof; its input, state, and retirement folds thread the byte memory
through mixed programs.  The stateful-machine equations and append bridges
reuse the existing `memNext`, `memAfter`, and `Rv32iBoundary.mem` semantics.

`MemRvfiTrace` is the raw certificate for that surface.  It admits arbitrary
invalid RVFI bubbles and requires the next retirement order plus an indexed
`Rv32iBoundary` witness for every load/store row.  Its normalization theorem
feeds the existing order-checked RVFI normalizer, and `trace_refines` identifies
the result with the profile-parametric stateful ISA trace for the same
threaded memory program.  `MemRvfiTrace.append` composes adjacent certificates
at the next retirement order and the exact threaded architectural and byte
memory state.  This is generic refinement infrastructure; the
PicoRV32 RTL remains parked at the existing unpacked `cpuregs` and
unsupported-member/net-z loader walls.

`MemRvfiCycleTrace` ties the same certificate to an actual
`RvfiCycleMachine`: bubble inputs remain arbitrary, while each retiring input
is definitionally the corresponding `memProgramInput`.  Its normalization,
`retireInputs_eq`, and `trace_refines` projections expose the machine's own
cycle stream to a future loaded-core invariant.

`MemRvfiCycleTrace.append` composes two such certificates at the exact
`rvfiStateAfter`/`memProgramState` boundary, carrying the first segment's
core state, byte memory, and next retirement order into the second segment.

## Current PicoRV32 re-probe on `github/master` 43a471fe3

The pinned YosysHQ source was freshly extracted again on 2026-11-07 without
RTL changes.  The source remains
`ef203c2b0a3fb793280f5114941416c425c5b461`; the current envelope is 2,992,422
bytes with SHA-256
`bbb534099237338b0c945ef56634407d9918a03f802a3fb1e11753d920a245be`.

At the recorded default parameters, the ordinary semantic route's exact first
refusal is:

```text
unsupported "Instantiate"
  "decl 'cpuregs': unpacked array storage outside E (UnpackedDecl:memory)"
```

The memory route advances past generated members but first refuses:

```text
unsupported "Instantiate"
  "memory cycle route does not yet admit unsupported module members"
```

The first retained member is the net-z wire `pcpi_mul_wr` at
`picorv32.v:257`.  This confirms the existing unpacked-memory and
unsupported-member/net-z walls; no new clean-room request or core adaptation
is justified.

The owned refinement layer now also includes
`LeanModels.Refine.RvfiBranchProgram`.  `BranchInstruction` retains the fetched
word, branch condition, source registers, offset, and decoder proof; the input,
architectural-state, and retirement folds preserve the exact conditional-branch
semantics for arbitrary lists.  `BranchRvfiTrace` and
`BranchRvfiCycleTrace` normalize raw RVFI observations, retain arbitrary bubble
inputs and cycle-step equalities, and identify the result with the stateful
RV32I machine trace.  Their append theorems compose adjacent certificates at
the exact architectural state, core state, and retirement-order boundary.
This is generic refinement infrastructure; the PicoRV32 RTL remains parked at
the existing unpacked `cpuregs` and unsupported-member/net-z loader walls.


The generic refinement layer now includes
`LeanModels.Refine.RvfiJumpProgram`.  `JumpInstruction` retains the fetched
word, semantic JAL/JALR kind, and decoder proof; the state and retirement folds
cover arbitrary mixtures of the two jump forms.  `JumpRvfiTrace` and
`JumpRvfiCycleTrace` normalize raw RVFI rows, retain arbitrary bubble inputs and
cycle-step equalities, and compose at the exact core, architectural-state, and
retirement-order boundary.  The bridges use the existing JAL/JALR target and
link-address semantics without introducing a second decoder.


`LeanModels.Refine.RvfiUpperProgram` now provides the corresponding
state-threaded LUI/AUIPC surface.  `UpperKind` keeps the two upper-immediate
forms distinct, while the program folds and raw/cycle RVFI certificates reuse
the exact writeback and pc semantics and compose at the same architectural and
retirement-order boundaries.

`LeanModels.Refine.RvfiFenceProgram` provides the matching state-threaded
`FENCE`/`FENCE.I` surface.  `FenceInstruction` retains the decoded fence kind
and fetched word; raw and cycle-aware certificates normalize arbitrary bubble
streams, retain the actual cycle inputs, and compose at the exact core,
architectural-state, and retirement-order boundaries.  Fence execution keeps
the threaded data memory unchanged through the existing profile-parametric
RV32I machine.

`LeanModels.Refine.RvfiSystemProgram` provides the corresponding no-interrupt
system-operation surface for `ECALL`, `EBREAK`, `MRET`, and `WFI`.
`SystemInstruction` retains the decoded operation and fetched word; its raw
and cycle-aware certificates preserve arbitrary bubbles, exact cycle inputs,
trap and return transitions, and the unchanged threaded data memory while
composing at the same core/state/retirement-order boundaries.

`LeanModels.Refine.RvfiCsrProgram` adds the implemented machine-mode Zicsr
surface.  `CsrInstruction` retains its CSR row, operation, decoder proof, and
row-lookup proof; raw and cycle-aware certificates preserve CSR readback,
WARL state updates, arbitrary bubbles, actual inputs, and the unchanged data
memory while composing at the same boundaries.  An absent CSR row remains
outside this certificate and follows the illegal-instruction boundary.

`LeanModels.Refine.RvfiIllegalProgram` supplies the corresponding
decode-failure trap certificate.  `IllegalInstruction` retains an undecodable
word and its proof; raw and cycle-aware certificates preserve the precise
illegal-instruction cause, trap handler transition, arbitrary bubbles, actual
inputs, unchanged data memory, and compositional core/state/order boundaries.

`LeanModels.Refine.RvfiTrapProgram` combines both illegal-instruction shapes
in one trap-program certificate: undecodable words and decoded Zicsr words
whose CSR rows are absent.  The indexed constructors retain the parser proofs
for each case while normalizing arbitrary bubbles and composing exact trap
transitions at the core, architectural-state, and retirement-order boundaries.

## Current PicoRV32 re-probe after generated-member admission (`bf85f330a`)

The pinned YosysHQ source was re-extracted on 2026-11-07 without RTL changes.
The semantic files used for the probe are identical to `origin/master` at
`27e7d5d62`, which contains the generated-member regression
`bf85f330a`; the later commits only add documentation.  The source remains
`ef203c2b0a3fb793280f5114941416c425c5b461`; the fresh envelope is 2,992,406
bytes with SHA-256
`bbdf7aee9e200a35f228adfa891eeaa10addb3b1608f3776f0bd9d61c42d4f9c`.

The declaration loads as a 26-parameter family with 216 declarations, 43
processes, and three generate entries.  The ordinary semantic route's exact
first refusal remains:

```text
unsupported "Instantiate"
  "decl 'cpuregs': unpacked array storage outside E (UnpackedDecl:memory)"
```

The memory route now admits the clean-room generated-member shapes, then first
refuses the PicoRV32 instance at the existing unsupported-module-member gate:

```text
unsupported "Instantiate"
  "memory cycle route does not yet admit unsupported module members"
```

Its first retained member is `NetSymbol:net-z` for `pcpi_mul_wr` at
`picorv32.v:257`.  No new clean-room request or core adaptation is justified;
the symbolic ADDI invariant remains parked at the unpacked `cpuregs` and
unsupported-member/net-z walls.

## 2026-11-08 PicoRV32 re-probe on the owner branch

The pinned YosysHQ source was re-extracted without RTL changes against the
owner lane's generated-member revision `ac176c933` (the public merge was still
pending at this probe).  The source remains
`ef203c2b0a3fb793280f5114941416c425c5b461`; the fresh envelope is 2,991,521
bytes with SHA-256
`5cf47d7aed28c2e63a0ab0dc3f3ac414f27fe326eab59ffe232b348bace45a3b`.

The declaration has 26 parameter declarations (18 local parameters), 189
declarations, 43 processes, and three generate entries.  The ordinary route's
exact first refusal remains:

```text
unsupported "Instantiate"
  "decl 'cpuregs': unpacked array storage outside E (UnpackedDecl:memory)"
```

The memory route passes the generated members and then first refuses:

```text
unsupported "Instantiate"
  "memory cycle route does not yet admit unsupported module members"
```

The first retained member is `NetSymbol:net-z` for `pcpi_mul_wr` at
`picorv32.v:257`.  This is an existing generic wall, so no new clean-room
request or RTL adaptation is justified; the symbolic ADDI invariant remains
parked at the unpacked-memory and unsupported-member/net-z boundaries.

## 2026-11-08 PicoRV32 re-probe after undriven-net admission (`3d11ff8f7`)

The pinned YosysHQ source was re-extracted without RTL changes against the
owner lane's memory-route revision `3d11ff8f7` (the public merge was still
pending at this probe).  The source remains
`ef203c2b0a3fb793280f5114941416c425c5b461`; the fresh envelope is 2,991,521
bytes with SHA-256
`5cf47d7aed28c2e63a0ab0dc3f3ac414f27fe326eab59ffe232b348bace45a3b`.

The ordinary route still first refuses the unpacked `cpuregs` memory:

```text
unsupported "Instantiate"
  "decl 'cpuregs': unpacked array storage outside E (UnpackedDecl:memory)"
```

The memory route admits the eight source-shaped PCPI `NetSymbol:net-z`
members, including `pcpi_mul_wr`, then first refuses:

```text
unsupported "Instantiate"
  "memory cycle route does not yet admit unsupported module members"
```

The first remaining denied member is the already catalogued
`IntegerLiteral:unsized-xz-parametric` (`'bx`) at `picorv32.v:1038`.
The generic x/z refusal family already has its own fixtures and oracle
records, so no duplicate clean-room request or RTL adaptation is justified;
the symbolic ADDI invariant remains parked at the unpacked-memory and
parametric-x/z boundaries.

## Mixed RV32I program certificate

`LeanModels.Refine.RvfiRv32iProgram` combines the admitted ALU, branch, jump,
memory, fence, system, implemented-CSR, and illegal/trap families in one
`Rv32iInstruction` union.  The mixed input, state, byte-memory, and retirement
folds expose append boundaries for arbitrary programs.  Its raw and
cycle-aware RVFI certificates consume the indexed `Rv32iBoundary`, preserve
bubbles and actual retiring inputs, and identify the normalized observations
with the stateful RV32I machine trace.  PicoRV32 remains blocked at the
unpacked `cpuregs` and unsupported-member/net-z loader boundaries.

The companion `rvfiCycleStepRefines_of_rv32i_program` constructor packages the
core-facing one-step invariant: each valid row identifies one mixed
instruction, its exact input, indexed post-state, and retirement; invalid rows
remain explicit ISA stutters.

## Constructing mixed cycle certificates from an invariant

`LeanModels.Refine.RvfiRv32iProgram` now defines
`Rv32iCycleStepRefines` and `rv32iRvfiCycleTrace_of_step`.  A loaded-core
invariant supplies the current order tag, exact cycle input, indexed mixed
boundary, and relation update for each valid row; invalid rows carry the
relation across an ISA stutter.  The constructor then produces a certificate
for every admitted finite cycle window, retaining every bubble input and core
state transition and threading the final relation to the mixed program state.
This is generic refinement infrastructure and does not model or extend a
finite PicoRV32 capture.

The companion `rv32iRvfiCycleTrace_of_step_refines` corollary now composes the
indexed step invariant with any admitted finite cycle window.  It returns the
mixed cycle certificate, the normalized equality to the stateful ISA trace,
and the final core-to-ISA relation in one quantified result.

## 2026-11-08 combined PicoRV32 memory/xz clean-room repro

Item 389 adds the source-shaped fixture
`Examples/system-verilog/cores/picorv32/walls/xz_memory.sv`.  It combines a
parameter-sized unpacked memory with a continuous assignment of the unsized
x/z literal `'bx`; it is a generic measurement fixture, not a rewrite of the
pinned YosysHQ source and not a new owner-lane request.

The approved pyslang-11 extractor emits a 9,020-byte envelope whose SHA-256 is
`cc40cd919372a91246472303ea75f1a9bb6cb569af0e4f9ad15161507fb3a610` (source
SHA-256 `b2f937bcacf45a96a2958dfc46c5b8239589dfcdc98c3e521f26bd4a04b0ed2f`).
The exact probe records the ordinary unpacked-memory refusal, the retained
`IntegerLiteral:unsized-xz-parametric`/`'bx` metadata, and the memory-route
`memory cycle route does not yet admit unsupported module members` refusal.
The owner-branch measurement at `3d11ff8f7` agrees and leaves the first denied
member in the already catalogued parametric x/z family.

## 2026-11-08 smaller RV32I census while PicoRV32 waits

The PicoRV32 memory-route request is waiting on the owner lane's generic
parametric `'bx` boundary.  I therefore ran the same admission census against
three smaller real RV32I cores, using pinned upstream trees, their upstream
source sets, the approved pyslang-11 extractor, and both current routes.  No
RTL was changed and all envelopes are outside this repository.

| core | upstream pin | top / source set | licence | envelope (bytes / SHA-256) | modules | static `Unsupported` nodes | extraction |
| --- | --- | --- | --- | ---: | ---: | ---: | ---: |
| FemtoRV32 Quark | [`BrunoLevy/learn-fpga`](https://github.com/BrunoLevy/learn-fpga) `f5ada24ae6cca67d99889daec2c4ee44a6e59417` | `FemtoRV32` / `FemtoRV/RTL/PROCESSOR/femtorv32_quark.v` | three-clause BSD (`FemtoRV/LICENSE.md`) | 751,470 / `9a97d6736c30221e580f898673adb6fcaa49931d24eec1494d006e040bdfc1ce` | 1 | 48 | 0.907 s |
| SERV | [`olofk/serv`](https://github.com/olofk/serv) `f200eb2ed7b69ac1c6b8eddd47654522aeee5ce8` | `serv_rf_top` / the 17 Verilog files in `serv.core`'s `core` fileset | ISC (`LICENSE`) | 2,055,412 / `ea713d68c00b6bc3cc4e892de56bf1ccc74d1ba2dcc9dc30abb9a317c64c7a64` | 14 | 71 | 3.200 s |
| DarkRISCV | [`darklife/darkriscv`](https://github.com/darklife/darkriscv) `bb6b483cc61a2886a0602c7e62b14f5995ddfbb9` | `darkriscv` / `rtl/darkriscv.v` with the checked-in `rtl/config.vh` include path | three-clause BSD (`LICENSE`) | 1,227,921 / `38b3c3253f79b006aac7a547d9c61fce31c86dfe26994a990ce324bd1ce321cf` | 1 | 1 | 1.178 s |

The exact `load_design_sv2` first refusals are:

* Quark: `REFUSED — our defaults elaboration disagrees with the envelope's resolved metadata (Lean vs slang differential): localparam 'FETCH_INSTR': Constant:untyped-width — an untyped parameter or localparam takes its expression's own type (IEEE 1800-2023 §6.20.2; slang, Yosys 0.53), while Icarus 12.0 gives it the lossless width of an expression built with + - * or ** ($bits of SB + 1'b1 with an 8-bit SB is 9, of N + 1 with an int N 33): the two are different constants wherever the width is observable (a concatenation part, a negative value extended into a wider unsigned context, a context it widens) — refused for every such untyped constant, at every point`.
* SERV: the same cross-check refusal, first at `parameter 'RF_WIDTH' default: Constant:untyped-width` (the route's source-shaped first refusal after supplying the recorded defaults is `localparam 'CSR_REGS': Constant:untyped-width`, with the same full message above).
* DarkRISCV: `REFUSED — our defaults elaboration disagrees with the envelope's resolved metadata (Lean vs slang differential): decl 'FLUSH': non-literal initializer outside the M0 tier`.

The route probes used the envelope parser directly after recording the
load-gate refusal, so they did not weaken or modify the differential gate.
At the default points Quark `[0, 24]` and DarkRISCV `[0]`, both the ordinary
`instantiateD2` route and `instantiateMemD2` return one loud
`unsupported "Instantiate"` process with, respectively, the Quark
`localparam 'FETCH_INSTR': Constant:untyped-width ...` and DarkRISCV
`decl 'FLUSH': non-literal initializer outside the M0 tier` messages.  SERV's
`defaultArgs` itself refuses at `parameter 'RF_WIDTH' default:
Constant:untyped-width`; with the source defaults supplied explicitly as
`[0, 0, 0, 0, 1, 1296649801, 0, 1, 1, 2, 10]`, both routes return one loud
`unsupported "Instantiate"` process at `localparam 'CSR_REGS':
Constant:untyped-width ...`.  No route reaches an admitted cycle design.

DarkRISCV is the closest follow-up by this measured admission distance: one
module and one static unsupported node, with only the declaration-initializer
wall.  Quark is next (one module, but 48 static unsupported nodes and 23
out-of-tier module members), and SERV is last (14 modules, 71 static nodes,
and the same untyped-width wall in a parameter/localparam chain).  The
DarkRISCV initializer is the smallest new real-core instance, so a clean-room
request was filed in the ls-sv inbox.  The external repro is
`logic [1:0] t = a;` with source SHA-256
`c6fd179b1c79448ed81918ef4b2d8f2b79b6cdbc891c96cbf10b8a08443351da` and
pyslang-11 envelope SHA-256
`6a649ad976ea82f8698cea10a41df120710f2a39fe07c90dbe4bc1cb66920cb6`.

## 2026-11-08 PicoRV32 re-probe after parametric x/z admission (`0050a0d69`)

The owner change `0050a0d69` is on public master.  Re-extracting the unchanged
PicoRV32 source commit
`ef203c2b0a3fb793280f5114941416c425c5b461` produces a byte-for-byte stable
2,991,505-byte envelope (source SHA-256
`0836050971b3c6cdd28ac3b1e5719a67fb645161912bef1e472e63995ceb0622`, envelope
SHA-256
`f636b29a893e51275f200d685b1feee4f2047f3c33fa733d0eb42b3f8c3e855c`).
`load_design_sv2` accepts one module with 26 parameters, 18 localparams, 216
declarations, 43 processes, three generate entries, and 32 retained metadata
entries.

At the recorded defaults, `instantiateD2` and `.sem` still stop at the
ordinary-route `cpuregs` unpacked-memory refusal.  The memory route admits the
PCPI net-z members and the unsized parametric `'bx` marker, then stops at
`ConversionExpression:xz-literal-parametric` for `1'bx` in
`picorv32.v:1132` (`decoded_imm <= 1'bx;`) with the exact result:

```text
unsupported "Instantiate"
  "memory cycle route does not yet admit unsupported module members"
```

This conversion-shaped wall is a new generic instance; a clean-room
parameter-sized memory repro was filed with ls-sv.  No candidate core currently
loads on the memory route, so the symbolic ADDI invariant remains parked.

## 2026-11-10 PicoRV32 re-probe on public master `df3b9105b`

The unchanged pinned source was re-extracted from
`ef203c2b0a3fb793280f5114941416c425c5b461` (source SHA-256
`0836050971b3c6cdd28ac3b1e5719a67fb645161912bef1e472e63995ceb0622`; envelope
SHA-256 `b615142a6876a7e1ae1e64526769330aa90f3c7cf197e00d8281b76b77ac8738`).
The ordinary route still first refuses `cpuregs` at `picorv32.v:203` with
`UnpackedDecl:memory`.  The memory route constructs 223 scalar declarations,
one unpacked memory, no initializers, and 52 processes, then reports the E
schedule walls `Schedule:preemptive` (processes 0/26) and
`Schedule:comb-source-order` (comb processes 9/25).  A guard-bypassed
diagnostic run returns 80 low-level states, but it is unvalidated until the E
scheduler closes those reports; no `MemCycle` change is made here.

## 2026-11-18 DarkRISCV external receipt

The fresh receipt for the pinned DarkRISCV source at
`darklife/darkriscv` commit `bb6b483cc61a2886a0602c7e62b14f5995ddfbb9`
records source SHA-256
`46d57b15cc42c0458e02500a2a30371cd4e7979970c27afd9d47c40d1fa8c1a0` and
envelope SHA-256
`5038a315ae61f44951ed400f61632ee29dfa30d7c1b092d5f5cddbafcd55243b`.
The approved `harness/rv/core_census.py` reports 206 admitted, 2 refused, and
0 not reached rows.  The refusals are the non-literal `FLUSH` initializer at
source line 247 and the `REGS[DPTR]` assignment target at source line 592.

The checked-in `darkriscv/check.py` and `darkriscv/nop_tb.sv` provide a
reproducible simulator-only witness for the unmodified source.  It drives the
core's instruction and data interfaces with a fixed NOP image and compares 220
cycle rows from Icarus Verilog 13.0 (`s20250103-64-gdad78d525`) and Xcelium
24.03-s004.  Both simulators agree on all 220 rows.  The normalized row
SHA-256 is
`8bb5b339ce1a3805726358b0fc27c35fa654edfb76441abe7c8d9010fea753dc`.

The checked-in `darkriscv/e_check.py` also runs `load_design_sv2` against the
pinned external envelope.  The envelope is accepted, and canonical E reports
`hasUnsupported = true` with one process carrying the exact `FLUSH` refusal.
The canonical-E result is therefore E-RUN 0/0.  The separate unpacked-memory
fixture remains a fixture receipt and is not counted as a DarkRISCV whole-core
E-RUN.  The checker accepts the two recorded envelope snapshots
`38b3c3253f79b006aac7a547d9c61fce31c86dfe26994a990ce324bd1ce321cf` and
`5038a315ae61f44951ed400f61632ee29dfa30d7c1b092d5f5cddbafcd55243b`.

## 2026-11-18 Quark external E-RUN blocker

The pinned FemtoRV32 Quark source is `BrunoLevy/learn-fpga` commit
`f5ada24ae6cca67d99889daec2c4ee44a6e59417`, with source SHA-256
`182e6d13bf5ab165b6eefaa22ae8d6a24ea45db6dd2dbd57dcfc5e81932097b7` and
envelope SHA-256
`b26f0bd9ca5cb9a40838bb7719ae9877876d572f02de076d52d4d9dc62c1efdc`.
Its approved census remains 1 module with 48 static unsupported nodes.  The
first canonical-E wall is the exact `FETCH_INSTR` untyped-width cross-check
refusal under IEEE 1800-2023 §6.20.2.

The checked-in `quark/check.py` attempts both pinned simulator compilers on the
unmodified source.  Icarus Verilog 13.0 and Xcelium 24.03-s004 both refuse
before elaboration because `instr` is used before its declaration at source
line 63.  Consequently Quark has E-RUN 0/0 and no simulator cycle rows.  No
source reorder or testbench workaround is admitted.  The existing DarkRISCV
and unpacked-memory receipts remain independent measurements.

The checked-in `quark/e_check.py` runs `load_design_sv2` against the pinned
external envelope and checks the same `FETCH_INSTR` untyped-width differential
refusal at elaboration.  It records canonical-E E-RUN 0/0 and accepts the two
recorded envelope snapshots
`9a97d6736c30221e580f898673adb6fcaa49931d24eec1494d006e040bdfc1ce` and
`b26f0bd9ca5cb9a40838bb7719ae9877876d572f02de076d52d4d9dc62c1efdc`.

## 2026-11-18 SERV simulator and E receipts

The pinned SERV source is `olofk/serv` commit
`f200eb2ed7b69ac1c6b8eddd47654522aeee5ce8`.  The checked-in
`serv/check.py` compiles the complete 17-file `serv.core` source set with
`RISCV_FORMAL` and instantiates `serv_rf_top` with `DEBUG=1`, which is the
configuration that drives SERV's RVFI outputs.  Its fixed instruction image
and ready memory interfaces produce 220 rows from each approved simulator.
Icarus Verilog 13.0 and Xcelium 24.03-s004 agree on every row.  The normalized
row SHA-256 is
`bbe7e48c24f4748f96beaf097df899183a5c15c0e7f51cad68d4057a034320ad`.

The checked-in `serv/e_check.py` runs `load_design_sv2` against the pinned
envelope `ea713d68c00b6bc3cc4e892de56bf1ccc74d1ba2dcc9dc30abb9a317c64c7a64`.
Canonical E refuses at the `RF_WIDTH` untyped-width differential under IEEE
1800-2023 §6.20.2, so SERV E-RUN is 0/0.  The source and envelope remain
external inputs, and the simulator and canonical-E receipts keep those inputs
hash-pinned.

## 2026-11-18 cross-core follow-up

The next two cores are DarkRISCV and FemtoRV32 Quark. They remain the nearest
general follow-ups in the recorded table. The fresh DarkRISCV receipt above
reports 206 admitted, 2 refused, and 0 not reached rows. Its canonical-E
receipt loads the pinned envelope and reports the `FLUSH` refusal, so E-RUN
remains 0/0. Quark remains at 1 module / 48 static unsupported nodes, with its
`FETCH_INSTR` untyped-width cross-check refusal. Its canonical-E receipt
records the same load-gate wall, while both simulators reject the source before
elaboration at the use-before-declared `instr` wall, so its E-RUN remains 0/0.

## 2026-11-18 census rerank after the R1 family

The required stall-rule rerank was rerun after the three theorem-only R1
families.  The approved core census reports the following current rows.

| core | census | canonical-E E-RUN | pinned simulator receipt | first actionable wall |
| --- | --- | --- | --- | --- |
| PicoRV32 | 360 admitted / 0 refused / 4 not reached | 0/220 cycles | Icarus 13.0 and Xcelium 24.03-s004: 220/220 | reactive dependency-order scheduler before cycle 0 |
| DarkRISCV | 206 admitted / 2 refused / 0 not reached | 0/0 cycles | Icarus 13.0 and Xcelium 24.03-s004: 220/220 | `FLUSH` non-literal initializer, then `REGS[DPTR]` target |
| FemtoRV32 Quark | 1 module / 48 static unsupported nodes | 0/0 cycles | both pinned simulators refuse before elaboration at use-before-declared `instr` | `FETCH_INSTR` untyped-width cross-check |
| SERV | 877 admitted / 74 refused / 48 not reached | 0/0 cycles | Icarus 13.0 and Xcelium 24.03-s004: 220/220 | `RF_WIDTH` untyped-width cross-check |

PicoRV32 remains the only loaded core with an input-driven canonical-E
execution attempt.  Its simulator rows are a source witness, while the
canonical-E run is still stopped by the exact scheduler refusal.  DarkRISCV,
Quark, and SERV have simulator or loader receipts but no canonical-E cycles.
The rerank therefore sends the next work to the highest safe ladder item,
the next complete PicoRV32 R1 family, until a general-lane scheduler landing
or a newly reachable real-design wall changes these measurements.

## 2026-11-18 aggregate-member red-fix handoff

The general SV lane's aggregate-member landing made master red in exhaustive
matches.  Its repair branch now contains the aggregate-member hierarchy rename
repair at commit `4a1b144aa`, which carries paths through the hierarchy rename
and closes the dependent proof cases.  A direct `lake env lean
LeanModels/Sv/CombHier.lean` on that branch exits successfully.  The named
module target build is otherwise clean apart from stale `#guard_msgs` replay
artifacts in the incremental Lake build.  No ls-sv2 semantics or RTL change is
needed for this cross-lane repair.

## 2026-11-18 source-overlay remeasurement

The pinned DarkRISCV checkout was re-extracted with the current approved
frontend and its include directory.  The source hash remains
`46d57b15cc42c0458e02500a2a30371cd4e7979970c27afd9d47c40d1fa8c1a0` and the
fresh envelope hash is
`ca8f0a92c7477ee9fd75f55966c122fa29400f8948a18ae361cc81a077077fc5`.  The
current census reports 176 admitted, 1 refused, and 0 not reached.  Canonical
E loads the envelope and reports the exact `FLUSH` non-literal initializer
refusal.  The pinned simulator witness remains 220/220 on Icarus Verilog 13.0
and Xcelium 24.03-s004, with normalized row hash
`8bb5b339ce1a3805726358b0fc27c35fa654edfb76441abe7c8d9010fea753dc`.

The pinned Quark checkout was re-extracted with its processor sources.  Its
source hash is `182e6d13bf5ab165b6eefaa22ae8d6a24ea45db6dd2dbd57dcfc5e81932097b7`
and the fresh envelope hash is
`ec5e14623631bce248ff56341e425721cd1242408a3279fd120c694e15fa74c2`.  The
current census reports 130 admitted, 51 refused, and 0 not reached.  Canonical E
refuses the envelope at the exact `FETCH_INSTR` untyped-width cross-check.
Icarus Verilog 13.0 and Xcelium 24.03-s004 both refuse the unmodified source
before elaboration because `instr` is used before its declaration, so Quark
E-RUN is 0/0.  These counts are a source-overlay measurement and do not replace
the earlier pinned envelope census in the table above.

The clean-room companion `darkriscv/walls/unary_initializer.sv` covers the
same constant form with `logic [1:0] value = -1`.  Its canonical-E probe now
loads without an unsupported declaration, and Icarus Verilog 13.0 and Xcelium
24.03-s004 both print `q=11`.  Re-running the DarkRISCV source-overlay census
after this landing moves it to 177 admitted, 0 refused, and 0 not reached.
The canonical-E source run advances to the next exact wall, the one-rank
unpacked `REGS` storage refusal.

The checked-in `darkriscv/e_check.py` accepts both the pre-landing envelope
receipts and the current source-overlay envelope
`ca8f0a92c7477ee9fd75f55966c122fa29400f8948a18ae361cc81a077077fc5`.  The
current receipt reports canonical-E E-RUN `0/0` at
`decl 'REGS': unpacked array storage outside E (UnpackedDecl:memory)`.  The
checked-in `quark/e_check.py` likewise accepts the current source-overlay
envelope `ec5e14623631bce248ff56341e425721cd1242408a3279fd120c694e15fa74c2`
and reports canonical-E E-RUN `0/0` at the unchanged `FETCH_INSTR`
untyped-width wall.  The pinned simulator receipts remain DarkRISCV `220/220`
on both approved simulators and Quark `0/0` because both simulators reject its
unmodified source before elaboration.

## 2026-11-18 one-rank memory wall handoff

The clean-room `darkriscv/walls/initial_memory.sv` has the same one-rank
unpacked storage shape as the DarkRISCV `REGS` declaration.  Icarus Verilog
13.0 and Xcelium 24.03-s004 both print `ROW q=3c` after the time-zero initial
write.  The ordinary canonical-E instantiation reports the exact refusal
`decl 'mem': unpacked array storage outside E (UnpackedDecl:memory)`.  Its
existing memory-route probe executes the source-shaped initial process and
reads the initialized cell, so this row is ready for the general lane's
canonical one-rank memory Step 12 branch.  No E memory meaning is changed in
this lane.

## 2026-11-18 R0 differential check

The pinned Sail RISC-V 0.13.1 oracle is not installed in this checkout, so no
Sail oracle result is claimed.  The RV harness self-test generated the same
257 cases across hash seeds with fingerprint
`a0d1ec3e980838c0c1fc997555fde11f25fd91d67687fc6c90a2fea5f4a0bc83`, and the
Lean-side coverage check covered all 57 decoder rows.

## 2026-11-18 canonical memory constant-initializer row

The clean-room `darkriscv/walls/memory_unary_initializer.sv` combines an
INT-class scalar initializer (`logic [1:0] value = -1`) with one-rank native
memory and a time-zero write.  The canonical E memory probe admits all six
rows in its census, retains the source-shaped initializer and continuous
assignment, and settles the cell and output to `11`.  Icarus Verilog 13.0 and
Xcelium 24.03-s004 both print `q=11`.

The change landed on public master as `af38185ce` after general-lane review.
It remains a general-lane CoreMemExec change, and it leaves the PicoRV32 census
and E-RUN counts unchanged.

## 2026-11-18 DarkRISCV current-master cycle probe

The public-master one-rank memory route was re-audited at commit
`1ffef29732e3d9e2737ab220f1c3364c8d8511ab` with the current DarkRISCV
source-overlay envelope.  `PDesign.instantiateCoreMem [0]` reports one memory
and 68 retained processes, and `CoreMemDesign.initialState` returns `ok`.
This is a real transition past the former `REGS` storage wall.

The next probe supplied one source-shaped input row with `CLK=0`, `RES=1`,
`IRQ=0`, `IDATA=0x00000013`, `IDACK=1`, `IBERR=0`, `DATAI=0`, `DDACK=1`, and
`DBERR=0`.  `CoreMemDesign.stepOnePassTrace` completed the reset-held pass
and a second pass with `RES=0`, returning the no-follow-up flag both times.
The checked-in receipt now records two completed canonical-E passes, while the
full `step` quiescence path remains unmeasured.

The post-audit census remains **177 admitted / 0 refused / 0 not reached**.
The public-master probe reproduces both successful passes.  Its first clock
transition remains a non-returning execution path in the bounded probe, so no
full E-RUN cycle is claimed.

## 2026-11-18 current source-overlay rerun

The two assigned follow-up inputs were fetched again at their pinned public
revisions and re-extracted with the approved Slang frontend.  DarkRISCV's
source SHA-256 is unchanged at
`46d57b15cc42c0458e02500a2a30371cd4e7979970c27afd9d47c40d1fa8c1a0`; the new
envelope is `a453663fe639176f1ff29d1aa3a1501dd1af0637551de625fe25c68b50f3f8c7`.
The census is **177 admitted / 0 refused / 0 not reached**.  Canonical E loads
the one-rank memory route and completes two passes, clock preparation, edge
execution, and NBA commit construction.  Its staged receipt is **4/4**, while
the first complete clock run remains unmeasured.  The pinned simulator receipt
remains **220/220** on both Icarus Verilog 13.0 and Xcelium 24.03-s004, with row digest
`8bb5b339ce1a3805726358b0fc27c35fa654edfb76441abe7c8d9010fea753dc`.

Quark's source SHA-256 is unchanged at
`182e6d13bf5ab165b6eefaa22ae8d6a24ea45db6dd2dbd57dcfc5e81932097b7`; the new
envelope is `19e757d78a76214d9b4e56a3fbfcd7ee98c303936d7d9f8a1a4dcdd8db72c519`.
The census is **130 admitted / 51 refused / 0 not reached**, while canonical E
refuses at the `FETCH_INSTR` untyped-width cross-check.  Both pinned simulators
still refuse before elaboration at the source's use-before-declared `instr`, so
Quark remains **E-RUN 0/0**.  The checker accepts these fresh envelope hashes
and preserves the exact refusal receipts.

The stage probe narrows that wall.  `prepareStep` succeeds for the first
`CLK=1, RES=0` row, `runEdges` succeeds across all 68 retained processes, and
the scalar plus memory NBA commit construction succeeds.  Settling the
post-commit state does not return within the same bound.  This is recorded as
an execution boundary, without assigning it an unsupported semantic message.

## 2026-11-18 DarkRISCV first clock transition

The next source-shaped probe threaded those two successful states into a third
row with `CLK=1`, `RES=0`, and the same ready instruction and data inputs.
`CoreMemDesign.stepOnePassTrace` did not return within a 180-second bounded
evaluation.  The reset-held and reset-released passes remain measured as 2/2,
while the first clock transition is an execution wall.  No canonical-E cycle
agreement is claimed for that transition.

## 2026-11-19 bounded first-clock receipt

`darkriscv/clock_wall_check.py` packages the staged receipt and the full
first-clock attempt.  It verifies the four completed stages first, then runs
the exact `stepOnePassTrace` from the reset-released state with the same
`CLK=1`, `RES=0`, ready instruction and data inputs.  The attempt has a
180-second bound.  A non-return is reported as an execution wall, and an
explicit `unsupported` result remains distinguishable from that wall.  This
receipt adds no simulator result and claims no complete DarkRISCV E-RUN cycle.

## 2026-11-19 current two-core census and E receipts

The pinned DarkRISCV source at `bb6b483cc61a2886a0602c7e62b14f5995ddfbb9` was
re-extracted with the approved Slang frontend and its `rtl` include directory.
The source hash is `46d57b15cc42c0458e02500a2a30371cd4e7979970c27afd9d47c40d1fa8c1a0`.
The fresh envelope hash is
`ddba565006335191c35955bd27c4c36ca134e57d8084864269b4a2f4fb77b96f`. The
census is **177 admitted / 0 refused / 0 not reached**. Canonical E completes
the two reset/input passes, clock preparation, edge execution, and both scalar
and memory NBA commit construction, giving a staged receipt of **4/4**. The
first complete clock transition remains an execution wall, so complete E-RUN is
**0/0**. Icarus Verilog 13.0 and Xcelium 24.03-s004 agree on the independent
simulator witness at **220/220** rows, with normalized digest
`8bb5b339ce1a3805726358b0fc27c35fa654edfb76441abe7c8d9010fea753dc`.

## 2026-11-19 DarkRISCV clock-edge refusal receipt

The current canonical-E receipt replays the pinned envelope through reset,
reset release, clock preparation, and the retained edge schedule. The first
clock edge reaches the exact known wall
`AssignmentExpression:target: REGS[DPTR] <= ...`, so the checker reports
staged reset and preparation success with complete E-RUN **0/0**. This is an
execution refusal at the source-shaped register-file target, not a simulator
disagreement or a completed cycle. The pinned Icarus Verilog 13.0 and Xcelium
24.03-s004 witness remains **220/220**.

The complete R1 consumer audit also passes for `r1_addi`, `r1_upper`,
`r1_jump`, `r1_branch`, `r1_alu`, `r1_alu_imm`, `r1_fence`, `r1_system`,
`r1_illegal`, `r1_csr`, `r1_mem`, `r1_mem_all`, and the RVFI adapter. These
kernel-checked consumers remain conditional on the loaded-core step and
progress premises, so the finite E-RUN receipt is not promoted to a universal
RTL invariant.

The pinned FemtoRV32 Quark source at
`f5ada24ae6cca67d99889daec2c4ee44a6e59417` was re-extracted with the approved
Slang frontend. The source hash is
`182e6d13bf5ab165b6eefaa22ae8d6a24ea45db6dd2dbd57dcfc5e81932097b7`, and the
fresh envelope hash is
`644b5ee318e42fe3362798172495e500cf001efeeded0b689eea4d7c9a355ccb`. The
census is **130 admitted / 51 refused / 0 not reached**. Canonical E refuses
at `FETCH_INSTR`'s untyped-width differential wall. Both pinned simulators
refuse the unmodified source before elaboration at the use-before-declared
`instr` diagnostic, so Quark remains **E-RUN 0/0**.

## 2026-11-19 fresh two-core census and E-RUN receipts

The two nearest open-core follow-ups were re-extracted from fresh checkouts at
their pinned revisions, with no RTL changes. The DarkRISCV envelope
(`5fdb97fc8b4f663d7265e2d3128610319ab6f2cfc86576cb1cee519c78e44ccc`) has a
source-overlay census of **177 admitted / 0 refused / 0 not reached**. Its
Icarus Verilog 13.0 and Xcelium 24.03-s004 rows agree on **220/220**, while
canonical E completes the staged reset, preparation, edge, and commit path
(4/4), then the source-shaped first-clock probe reaches its 180-second exact
step timeout. Its complete E-RUN is therefore **0/1** for that probe.

The Quark envelope
(`644b5ee318e42fe3362798172495e500cf001efeeded0b689eea4d7c9a355ccb`) has a
source-overlay census of **130 admitted / 51 refused / 0 not reached**.
Canonical E refuses at the `FETCH_INSTR` untyped-width differential wall.
Icarus Verilog 13.0 and Xcelium 24.03-s004 both refuse the unchanged source
before elaboration at the use-before-declared `instr`, so Quark E-RUN is
**0/0**.

## 2026-11-19 DarkRISCV dynamic memory NBA execution wall

The clean-room fixture `darkriscv_dynamic_memory_nba.sv` preserves the first-clock
shape reached in the pinned DarkRISCV source.  It uses a one-rank unpacked
`REGS` memory, a run-time `DPTR` index, and a nonblocking assignment in the
`posedge CLK` process.  The testbench drives reset, writes `32'h000000a5` to
`REGS[2]`, then writes `32'h0000005a` to `REGS[1]`.

Icarus Verilog 13.0 and Xcelium 24.03-s004 both print the same four rows.  The
registers begin as x, the first write is visible after its clock edge, and the
second write preserves `REGS[2]`.  The canonical-E probe loads the fixture and
returns the same final memory cells, `REGS[2] = 32'h000000a5` and
`REGS[1] = 32'h0000005a`.  No whole-core DarkRISCV E-RUN result is claimed by
this clean-room receipt.

## 2026-11-19 DarkRISCV system-function expression wall

The repository-local clean-room fixture `darkriscv/walls/function_call_expression.sv`
retains the parser's source-shaped `$test$plusargs("flag")` expression inside an
`always_comb` assignment.  Icarus Verilog 13.0 and Xcelium 24.03-s004 agree on
both input rows with no plusarg and with `+flag`.  Without the plusarg the
outputs are `0, 0`, and with it they are `0, 1` for inputs `0, 1`.

The symbolic envelope is `077ff21c54062b54502c686f88f7953014b178a6e9b3f41a76db275d3f9938d4`.
Canonical E loads the envelope, then refuses the first execution with
`unsupported expression 'SysCall'`.  This is the current E boundary for the
parser-retained system-function expression.  No whole-core DarkRISCV E-RUN
result is claimed by this clean-room receipt.

## 2026-11-19 member-element-index receipt correction

The earlier wall-table status for the generated packed-member element index is
now superseded by the canonical-E receipt in
`Examples/system-verilog/sem2/member_index_canonical_e/`.  Its source-shaped
`state.out_dis[i]` case retains the member index under the generated body and
runs seven known, x, and z rows.  Icarus Verilog 13.0, Xcelium 24.03-s004, and
canonical E agree on `x, 0, 1, 0, x, z, 1`.  The member-element-index clean-room
wall is therefore closed for this shape.  No real-core census count is claimed
by this correction.

## 2026-11-20 dynamic member-element-index wall

The repository-local `sem2/member_elem_loud` clean-room source retains a
run-time element index through a packed struct member, `p.bytes[i_i]`, under
IEEE 1800-2023 §11.5.1.  Canonical E loads the parser-shaped node, then refuses
initial-state construction with the exact message
`unsupported expression 'ElementSelectExpression:member-index'`.  The
executable E guard is
`darkriscv/walls/member_element_index_probe.lean`.

Icarus Verilog 13.0 refuses the unchanged source during elaboration with
`Array/part index expressions must be constant here`.  Xcelium 24.03-s004
accepts it and produces the dynamic member rows `00011000`, `00100100`,
`01000010`, and `10000001` for indices 0 through 3 on packed bytes
`81 42 24 18`; all-x and all-z member data produce all-x and all-z outputs.
The refusal is therefore retained exactly in E, with no simulator value
substituted for the unsupported node.
