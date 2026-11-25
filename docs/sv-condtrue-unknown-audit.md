# condTrue unknown-branch audit

This inventory records proved statements whose observable result depends on the current
implementation rule that an unknown condition has `condTrue = false` and therefore takes
the else branch. The owner’s x principle requires a per-read 0/1 resolution, so these
statements need a relational bridge or revision before they can support an x-sensitive
theorem.

## Explicit unknown-branch statements

- `Examples/system-verilog/seq_cycle/reset_for_proof.lean`: `RzClaim`,
  `rzClaim_of_runF`, `rz_cycle`, `rz_runs`, and the derived
  `rz_read_after_reset` and `rz_runs_reset`. The claim says a false reset condition
  runs the write-enable branch, and the source comments explicitly classify reset and
  write-enable x/z as false.
- `Examples/system-verilog/seq_cycle/rf_proof.lean`: `rf_no_write`. Its hypothesis
  `we.condTrue = false` is documented as covering 0, x, and z, and the conclusion
  says the memory is unchanged.
- `Examples/system-verilog/cores/picorv32/picorv32_regs_refines.lean`:
  `picorv32_regs_unknown_wen_step`. It instantiates `wen = 1'bx`, proves the write
  is skipped, and proves both read ports retain their pre-edge values.
- `Examples/system-verilog/seq_cycle/gen_proof.lean`: `gb_hold`.
- `Examples/system-verilog/seq_cycle/unsigned_proof.lean`: `ue_hold`.
  Both use a false enable condition as the hold case, including x/z.
- `Examples/system-verilog/first_theorem/dff_arst_proof.lean`: `dff_load`
  accepts a reset bit other than 0, including x/z, and relies on the negated reset
  condition taking its else branch.
- `Examples/system-verilog/seq_cycle/plain_proof.lean`: `pa_load` and
  `pa_keep`. Their hypotheses classify reset and enable x/z through the false
  `condTrue` cases.
- `Examples/system-verilog/case_inside/proof.lean`: `ambiguous_then_match`
  rewrites an ambiguous case result `.lx` to `condTrue = false) and skips the
  first arm.
- `Examples/system-verilog/immediate_assertions/proof.lean`: `failure_retains`
  and `cover_skips`, whose `condTrue = false) hypotheses include ambiguous values.
- `Examples/system-verilog/xsel/proof.lean`: `xsel_x_raw` and `xsel_x_else`
  explicitly claim that x/z selects the else arm.

## Transitive cycle and run theorems

These theorems state a cycle function or trace whose value contains a `condTrue`-guarded
branch, or derive their run/refinement result from one of those cycle theorems.

- `Examples/system-verilog/seq_cycle/cnt_proof.lean`: `cnt_cycle`,
  `cnt_trace`, `cntClaim_of_trace`, `cnt_runs`.
- `Examples/system-verilog/seq_cycle/valid_proof.lean`: `vc_cycle`,
  `vc_trace`, `vcClaim_of_trace`, `vc_runs`.
- `Examples/system-verilog/seq_cycle/amem_proof.lean`: `am_eqs`,
  `amClaim_of_runSat`, `am_runs`.
- `Examples/system-verilog/seq_cycle/arst_proof.lean`: `arst_cycle`,
  `arstClaim_of_runF`, `arst_runs`.
- `Examples/system-verilog/seq_cycle/gen_proof.lean`: `gb_reg_row`,
  `gb_reg_step`.
- `Examples/system-verilog/seq_cycle/unsigned_proof.lean`: `ue_row`,
  `ue_step`.
- `Examples/system-verilog/seq_cycle/plain_proof.lean`: `pa_row`, `ff_row`,
  `pa_eq_ff`, `pa_step`.
- `Examples/system-verilog/seq_cycle/rf_proof.lean`: `rf_cycle`,
  `rfClaim_of_runF`, `rf_runs`, and the `rf_runs_raw corollary.
- `Examples/system-verilog/first_theorem/dff_arst_proof.lean`: `dff_row`,
  `dff_step`, and `dff_load`.
- `Examples/system-verilog/counter/proof.lean`: `counter_cycleStep`,
  `counter_runFrom`, `counter_run`, `counter_total`, `counter_det`,
  `counter_step_ofBitVec`, `counterTrace_model_column`,
  `counterTrace_from_reset`, `counter_from_reset`, `counter_refines`,
  and `counter_runs.
- `Examples/system-verilog/toggle/proof.lean`: `toggle_cycleStep`,
  `toggle_runFrom`, `toggle_run`, `toggle_total`, `toggle_runs`,
  `toggle_det`, `toggle_step_ofBool`, `toggleTrace_model_column`,
  `toggleTrace_from_reset`, `toggle_from_reset`, and
  `toggle_refines_model`.
- `Examples/system-verilog/xsel/proof.lean`: `xsel_combPass`,
  `xsel_combSettle`, `xsel_cycleStep`, `xsel_runFrom`, `xsel_run`,
  `xsel_total`, `xsel_det`, `xselTrace_snapshots`, `xsel_x_raw`,
  `xsel_x_else`, and `xsel_runs`.

## Evaluator and bridge equations

These proved equations expose the same implementation choice and must be treated as
executor equations when the relational semantics is introduced.

- `LeanModels.Sv.Kernel.Core0Proc.execBody_if_run`
- `LeanModels.Sv.Loop2Frag.Denotes.ite`
- `LeanModels.Sv.Loop2E.DenotesE.ite`
- `LeanModels.Sv.Comb2Proc.evalPure2_ifGuard`
- `LeanModels.Sv.ToggleExample.LVec.condTrue_ofLogic`

The resolution-aware bridges
`Core0Resolve.execBody_if_resolved`, `Core1Resolve.execFF_if_resolved`,
`Core1Resolve.execFF_if_xread`, and `MemEResolve.memE_if_xread` require an explicit
resolution or a known result. They do not themselves assert that an unknown takes the
else branch.

## Excluded known-only results

The following nearby theorems only reason about known 0/1 inputs or widths and do not
make the unknown-else claim: `dff_reset`, `arstStep_known`, `arstF_known`,
`cntNext_reset`, `cntNext_count`, `gb_load`, `ue_load_known`,
`rf_read_after_write`, `rf_read_other`, `rz_read_after_reset's direct
known-reset implication, and the width/structure/port lemmas. Their proofs may still
transitively use an affected run theorem and should be rechecked when that theorem is
migrated.

