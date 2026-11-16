import Examples.«system-verilog».gen_lpsum.gen
import LeanModels.Sv.CombViewTactic

/-!
# The parameter stage node by node (`Examples/system-verilog/gen_lpsum`)

At a symbolic `N` the parameter stage of `gen_lpsum` binds its three localparams from the lemmas of the nodes of their
initializers (`closeParamEnvComp`): the 24 `?:` of `S` and its partial sums, `2 * S - S`, `(N < 2) ? 2 : N`, each node's
value placed in the 32-bit range by bounds composed from its operands' (a parameter's bounds by `omega`). With
`set_option sv_comb.lp_atoms true` every obligation reads the localparams as variables (`hlp_S`, `hlp_D`, `hlp_NP`);
`sv_ite_bounds` bounds each `?:` of their definitions (`0 ≤ S ≤ 24` is then linear), and `sv_ite_omega` splits a
condition only where `omega` still needs it. The automatic closers are off (`sv_comb.auto_close false`): tried on each
goal before the bounds are in context, they would split the 24 `?:` of `hlp_S`.

Build: `lake build Examples.«system-verilog».gen_lpsum.comb_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_lpsum.gen

namespace Examples.«system-verilog».gen_lpsum.comb_proof

set_option sv_comb.lp_atoms true in
set_option sv_comb.auto_close false in
set_option maxHeartbeats 1000000 in
/-- The structure of `gen_lpsum` and its rank (every site reads the input only), at every `1 ≤ N < 2^20`. -/
theorem gen_lpsum_struct (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) :
    CombDesign (gen_lpsum.sem N) ∧ Acyclic (gen_lpsum.sem N) := by
  sv_structure (lexRank := fun _ => (0, 0, 0))
  all_goals (sv_ite_bounds; sv_ite_omega)

/--
info: 'Examples.«system-verilog».gen_lpsum.comb_proof.gen_lpsum_struct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_lpsum_struct

end Examples.«system-verilog».gen_lpsum.comb_proof
