import LeanModels.Sv.CombTask

/-!
# The multiplier statement of the Dadda record (`mul_dadda`)

`MulStatement sem` is the svGolf `mul` task's statement (`svgolf/tasks/mul/Spec.lean` over `svgolf/SvGolf/Task.lean`:
`CombTask.Statement`, its three conjuncts `Interface`, `Unclocked ∧ LoopFree ∧ Terminates2` and `Computes`), restated
over ls-sv alone, because `LeanModels` may not import `svgolf` (as `prefix_ks/statement.lean` restates the `add` task and
`clmul_kara/statement.lean` the `clmul` task). `HoldAll` over the task's port lists is one `SvState.lookup` equation per
port, `Unclocked` and `LoopFree` are their definitions, the ports are `Design2.inputPorts`/`outputPorts`
(`CombTask.lean`), and the range is the task's `1 ≤ N < 2^30` (the output width `2N`, an `int` expression of the module,
stays below `2^31`). For every `N` in range:

1. the input ports are exactly `a`, `b` (`N` bits) and the output port exactly `p` (`2N` bits), names, order and
   widths;
2. no process is clocked, the design lowers to continuous assigns with a rank (no combinational loop), and every run
   under every schedule and stimulus completes;
3. in every completed run, every cycle whose stimulus entry drives `a`, `b` with known values `a b : BitVec N` ends in a
   snapshot holding on `p` the full product `a * b`, the natural-number product of the two unsigned inputs as a `2N`-bit
   vector (nothing is truncated: the product of two `N`-bit numbers is below `2^(2N)`).
-/

namespace Examples.«system-verilog».mul_dadda.statement

open LeanModels.Sv

/-- **The svGolf `mul` statement over ls-sv** (see the module docstring). -/
def MulStatement (sem : Nat → Design2) : Prop :=
  ∀ N, 1 ≤ N ∧ N < 2 ^ 30 →
    ((sem N).inputPorts = [("a", N), ("b", N)] ∧ (sem N).outputPorts = [("p", 2 * N)]) ∧
      ((∀ p ∈ (sem N).processes.toList, p.isEdgePhase = false) ∧
        (∃ d', (sem N).lowerComb = some d' ∧ Acyclic d') ∧ Terminates2 (sem N)) ∧
      sem N ⊨₂ spec2 fun stim tr =>
        ∀ (c : Nat) (inputs st : SvState), stim[c]? = some inputs → tr[c]? = some st →
          ∀ (a b : BitVec N),
            SvState.lookup inputs "a" = some (LVec.ofBitVec a) →
            SvState.lookup inputs "b" = some (LVec.ofBitVec b) →
            SvState.lookup st "p" = some (LVec.ofBitVec (BitVec.ofNat (2 * N) (a.toNat * b.toNat)))

/-! The task's own sanity rows (`Spec.lean`): `15 * 15 = 225` at `N = 4`, `255 * 255 = 65025` at `N = 8`, `3 * 3 = 9`
at `N = 2` (the top bit is used), evaluated here by the compiler. -/
#guard BitVec.ofNat (2 * 4) ((15#4).toNat * (15#4).toNat) == 225#8
#guard BitVec.ofNat (2 * 8) ((255#8).toNat * (255#8).toNat) == 65025#16
#guard BitVec.ofNat (2 * 2) ((3#2).toNat * (3#2).toNat) == 9#4

end Examples.«system-verilog».mul_dadda.statement
