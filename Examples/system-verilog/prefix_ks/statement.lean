import LeanModels.Sv.CombTask

/-!
# The adder statement of the prefix-adder examples (`prefix_ks`, `prefix_sklansky`)

`AddStatement sem` is the svGolf `add` task's statement (`svgolf/tasks/add/Spec.lean` over `svgolf/SvGolf/Task.lean`:
`CombTask.Statement`, its three conjuncts `Interface`, `Unclocked ∧ LoopFree ∧ Terminates2` and `Computes`), restated
over ls-sv alone, because `LeanModels` may not import `svgolf`. The restatement unfolds svGolf's vocabulary and changes
nothing else: `HoldAll` over the task's port lists is one `SvState.lookup` equation per port, `Unclocked` and
`LoopFree` are their definitions, the ports are `Design2.inputPorts`/`outputPorts` (`CombTask.lean`, svGolf's
`inputPorts`/`outputPorts` verbatim), and the range is the task's `1 ≤ N < 2^20`. For every `N` in range:

1. the input ports are exactly `a`, `b` (`N` bits) and `cin` (1 bit), and the output ports exactly `s` (`N` bits) and
   `cout` (1 bit), names, order and widths;
2. no process is clocked, the design lowers to continuous assigns with a rank (no combinational loop), and every run
   under every schedule and stimulus completes;
3. in every completed run, every cycle whose stimulus entry drives `a`, `b`, `cin` with known values `a b : BitVec N`,
   `cin : BitVec 1` ends in a snapshot holding `s = t mod 2^N` and `cout = t / 2^N`, `t = a + b + cin` in `Nat`.

`addExhaustive` is a test, not part of the statement: every input combination at a small width, one `run2` cycle, its
outputs against `Nat` arithmetic (the `#guard` rows of each example's `gen.lean`).
-/

namespace Examples.«system-verilog».prefix_ks.statement

open LeanModels.Sv

/-- **The svGolf `add` statement over ls-sv** (see the module docstring). -/
def AddStatement (sem : Nat → Design2) : Prop :=
  ∀ N, 1 ≤ N ∧ N < 2 ^ 20 →
    ((sem N).inputPorts = [("a", N), ("b", N), ("cin", 1)] ∧
        (sem N).outputPorts = [("s", N), ("cout", 1)]) ∧
      ((∀ p ∈ (sem N).processes.toList, p.isEdgePhase = false) ∧
        (∃ d', (sem N).lowerComb = some d' ∧ Acyclic d') ∧ Terminates2 (sem N)) ∧
      sem N ⊨₂ spec2 fun stim tr =>
        ∀ (c : Nat) (inputs st : SvState), stim[c]? = some inputs → tr[c]? = some st →
          ∀ (a b : BitVec N) (cin : BitVec 1),
            SvState.lookup inputs "a" = some (LVec.ofBitVec a) →
            SvState.lookup inputs "b" = some (LVec.ofBitVec b) →
            SvState.lookup inputs "cin" = some (LVec.ofBitVec cin) →
            SvState.lookup st "s" = some (LVec.ofBitVec (BitVec.ofNat N (a.toNat + b.toNat + cin.toNat))) ∧
            SvState.lookup st "cout" =
              some (LVec.ofBitVec (BitVec.ofNat 1 ((a.toNat + b.toNat + cin.toNat) / 2 ^ N)))

/-- Every known input combination at width `N` under schedule `σ`: the one-cycle run completes, and its snapshot holds
`(a + b + cin) mod 2^N` on `s` and `(a + b + cin) / 2^N` on `cout` (a test, evaluated by the compiler). -/
def addExhaustive (sem : Nat → Design2) (σ : ScheduleOracle) (N : Nat) : Bool :=
  (List.range (2 ^ (2 * N + 1))).all fun k =>
    let a := k % 2 ^ N
    let b := k / 2 ^ N % 2 ^ N
    let ci := k / 2 ^ (2 * N)
    match run2 (sem N) σ 64 [[("a", LVec.ofNat N a), ("b", LVec.ofNat N b), ("cin", LVec.ofNat 1 ci)]] with
    | .ok [st] =>
        SvState.lookup st "s" == some (LVec.ofNat N ((a + b + ci) % 2 ^ N)) &&
          SvState.lookup st "cout" == some (LVec.ofNat 1 ((a + b + ci) / 2 ^ N))
    | _ => false

end Examples.«system-verilog».prefix_ks.statement
