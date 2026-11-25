# X-dependent SystemVerilog claims

This is a static audit of proved statements that call the executor's
`condTrue` on a value that may be x or z. It is preparation for the
relation migration. It does not change the current executor meaning and it
claims no new simulator result.

The owner ruling is per-read resolution. At an x or z decision, both 0 and 1
are admissible when the IEEE rule leaves the decision open. A theorem that
uses the current `condTrue` else branch as a universal result needs a
known-decision premise or a set-valued postcondition.

## Confirmed x-dependent claims

| Source and theorem surface | Current content | Required migration |
| --- | --- | --- |
| `Examples/system-verilog/seq_cycle/reset_for_proof.lean`, `RzClaim`, `rzClaim_of_runF`, `rz_runs`, `rz_runs_reset` | The claim splits on `rst.condTrue`. The false arm includes x and z, so an unresolved reset is treated as the write-enable false arm. | **Migrated:** reset and write equations are exposed only under `DecisionKnown` premises, and `rz_runs_reset` carries the reset-knownness premise. The `N ≤ 4000` premise remains a separate executor-fuel debt. |
| `Examples/system-verilog/seq_cycle/amem_proof.lean`, `body`, `am_eqs`, `am_runs` | `!rstn` is projected through `condTrue`. An unresolved reset therefore selects the data-write arm in the current equation. The run claim allows coherent x starts and four-state stimulus. | **Migrated:** `AmStep` and `AmClaim` now require `DecisionKnown` for the current reset read, and the asynchronous predecessor case requires it for the previous reset read. |
| `Examples/system-verilog/seq_cycle/rf_proof.lean`, `rfF`, `rf_cycle`, `rf_runs` | An x or z write-enable takes the no-write branch. The file's prose calls this the exact E rule, but it is the historical executor rule. | Use the relation's two possible write outcomes, or require a known write-enable. |
| `Examples/system-verilog/cores/picorv32/picorv32_regs_refines.lean`, `picorv32_regs_unknown_wen_step` | The theorem explicitly proves that `wen = 1'bx` leaves memory unchanged. | Restate as a permitted-outcome theorem or restrict `wen) to known values. |
| `Examples/system-verilog/xsel/proof.lean`, `xsel_combPass`, `xsel_run`, `xsel_x_else` | The mux result is `if sel.condTrue then a else b`, and the prose explicitly says x/z selects b. | Replace the x-select result with the relation's outcome set. Keep the known-select theorem as a singleton projection. |
| `Examples/system-verilog/counter/proof.lean`, `counterTrace`, `counter_run`, `counter_refines` | Reset is read through `condTrue) for every stimulus and the all-x startup. An x reset is silently treated as not asserted. | Add known-reset assumptions or quantify over both reset decisions. |
| `Examples/system-verilog/toggle/proof.lean`, `toggleTrace`, `toggle_run`, `toggle_refines` | Reset and enable both use `condTrue) over the all-x startup and arbitrary stimulus. | Add known-control assumptions or a set-valued relation theorem. |
| `Examples/system-verilog/seq_cycle/arst_proof.lean`, `arstF`, `arst_runs` | Asynchronous reset and enable are selected through `condTrue) while the documented rows include x and z controls. | Carry per-read reset and enable witnesses, then retain the known-control corollaries. |

These entries are findings about theorem statements and their definitions. They
are not claims that the current differential rows disagree with a simulator.
Existing rows must be re-run as relation membership rows after the resolution
relation is connected.

## Review-needed uses

The following files contain `condTrue` in symbolic equations or helper
lemmas, but the surrounding theorem may already provide known-value
hypotheses. Inspect the statement before migration.

* `Examples/system-verilog/seq_cycle/plain_proof.lean`
  (`pa_step`, `pa_reset`, `pa_load`, `pa_keep)).
* `Examples/system-verilog/seq_cycle/gen_proof.lean`
  (`gb_reg_step`, `gb_wire_row), and the conditional helper lemmas).
* `Examples/system-verilog/seq_cycle/valid_proof.lean`
  (`valid_step` and its reset/ready branches).
* `Examples/system-verilog/seq_cycle/unsigned_proof.lean`
  (`ue_step`, `ue_load_known`, and `ue_hold`).
* `Examples/system-verilog/first_theorem/dff_arst_proof.lean`
  (the asynchronous-reset next-state equation).
* `LeanModels/Sv/CombFragE.lean`, `Seq2Cycle.lean`, `Loop2Frag.lean`,
  `Loop2E.lean`, `MemCycle.lean), and `Sva.lean). These are executor or
  compatibility definitions whose users need a known-decision bridge.

The known-value proof route remains valid. `DecisionKnown) and
`decisionKnown_of_allKnown` in `Kernel/XResolve.lean) are the intended
interim witnesses. No proof may use `condTrue)'s x-optimistic branch without
one of those witnesses once the relation migration begins.

## Audit boundary

The audit covers source-visible Lean definitions and theorem statements under
`LeanModels/Sv` and `Examples/system-verilog`. It does not edit generated
envelopes, alter a simulator row, or decide any open hardware-layer question.
The next semantic migration must add relation membership rows for the
confirmed entries and preserve equality rows where all decisions are known.

