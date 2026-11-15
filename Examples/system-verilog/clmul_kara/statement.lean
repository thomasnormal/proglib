import LeanModels.Sv.CombTask

/-!
# The carry-less multiplier statement of the Karatsuba record (`clmul_kara`)

`ClmulStatement sem` is the svGolf `clmul` task's statement (`svgolf/tasks/clmul/Spec.lean` over
`svgolf/SvGolf/Task.lean`: `CombTask.Statement`, its three conjuncts `Interface`, `Unclocked ∧ LoopFree ∧ Terminates2`
and `Computes`), restated over ls-sv alone, because `LeanModels` may not import `svgolf` (as `prefix_ks/statement.lean`
restates the `add` task). `ofBits` and `coeff` are the task's definitions verbatim; `HoldAll` over the task's port lists
is one `SvState.lookup` equation per port, `Unclocked` and `LoopFree` are their definitions, the ports are
`Design2.inputPorts`/`outputPorts` (`CombTask.lean`). The range is the record's, `1 ≤ N < 2^16` (the task's is
`N < 2^30`; the record's localparam `T = 3 ** L` and the row widths `4·T`, `8·T` are 32-bit `int`s, which bounds its
own range). For every `N` in range:

1. the input ports are exactly `a`, `b` (`N` bits) and the output port exactly `p` (`2N - 1` bits), names, order and
   widths;
2. no process is clocked, the design lowers to continuous assigns with a rank (no combinational loop), and every run
   under every schedule and stimulus completes;
3. in every completed run, every cycle whose stimulus entry drives `a`, `b` with known values `a b : BitVec N` ends in a
   snapshot holding on `p` the coefficients of the product of the two polynomials over GF(2) that `a` and `b` encode:
   bit `k` of `p` is the XOR, over the pairs `i + j = k` with `i, j < N`, of `a_i AND b_j` (`coeff`).
-/

namespace Examples.«system-verilog».clmul_kara.statement

open LeanModels.Sv

/-- The `n`-bit vector whose bit `k` (counted from the least significant end) is `f k` (the svGolf task's `ofBits`). -/
def ofBits : (n : Nat) → (Nat → Bool) → BitVec n
  | 0, _ => 0#0
  | n + 1, f => ofBits n (fun k => f (k + 1)) ++ BitVec.ofBool (f 0)

/-- Coefficient `k` of the product polynomial: the XOR, over all pairs `(i, j)` of positions below `N` with `i + j = k`,
of `a_i AND b_j` (the svGolf task's `coeff`). -/
def coeff (N : Nat) (a b : BitVec N) (k : Nat) : Bool :=
  (List.range N).foldl (fun acc i =>
    (List.range N).foldl (fun acc j => acc ^^ (decide (i + j = k) && a.getLsbD i && b.getLsbD j)) acc) false

/-- **The svGolf `clmul` statement over ls-sv, at the record's range** (see the module docstring). -/
def ClmulStatement (sem : Nat → Design2) : Prop :=
  ∀ N, 1 ≤ N ∧ N < 2 ^ 16 →
    ((sem N).inputPorts = [("a", N), ("b", N)] ∧ (sem N).outputPorts = [("p", 2 * N - 1)]) ∧
      ((∀ p ∈ (sem N).processes.toList, p.isEdgePhase = false) ∧
        (∃ d', (sem N).lowerComb = some d' ∧ Acyclic d') ∧ Terminates2 (sem N)) ∧
      sem N ⊨₂ spec2 fun stim tr =>
        ∀ (c : Nat) (inputs st : SvState), stim[c]? = some inputs → tr[c]? = some st →
          ∀ (a b : BitVec N),
            SvState.lookup inputs "a" = some (LVec.ofBitVec a) →
            SvState.lookup inputs "b" = some (LVec.ofBitVec b) →
            SvState.lookup st "p" = some (LVec.ofBitVec (ofBits (2 * N - 1) (coeff N a b)))

/-! `(x + 1)^2 = x^2 + 1` over GF(2) at `N = 2`, and FIPS 197 Section 4.2's `{57} * {83}` unreduced (the task's own
sanity rows, evaluated here by the compiler). -/
#guard ofBits 3 (coeff 2 0b11#2 0b11#2) == 0b101#3
#guard ofBits 15 (coeff 8 0x57#8 0x83#8) == 0x2b79#15

end Examples.«system-verilog».clmul_kara.statement
