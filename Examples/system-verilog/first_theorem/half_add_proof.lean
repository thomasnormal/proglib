import LeanModels.Sv.Ingest2
import LeanModels.Sv.Comb2
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombProcTactic

/-!
# A combinational module, for every width, by `sv_structure` + `sv_equations`

The combinational worked example of `README.md` in this directory. The design is `half_add.sv`, a `W`-bit array of
half adders written with continuous assignments:

```systemverilog
module half_add #(parameter int W = 4)
  (input logic [W-1:0] a, b, output logic [W-1:0] s, c);
  assign s = a ^ b;
  assign c = a & b;
endmodule
```

To adapt the file to another combinational module: change the envelope path, the port names and the output functions.

The envelope is generated, never edited. From the repository root:

```console
$ python3.12 extractors/sv/extract.py --top half_add Examples/system-verilog/first_theorem/half_add.sv \
    -o Examples/system-verilog/first_theorem/half_add.sv.json
```

Oracle: Icarus Verilog 12.0 (stable), the testbench in `README.md`, on the two rows of the run below at `W = 4`
(the second with an x and a z input bit): both agree.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombEq

namespace Examples.«system-verilog».first_theorem.half_add_proof

load_design_sv2 ha from "Examples/system-verilog/first_theorem/half_add.sv.json"

-- Non-vacuity: a compiled run at W = 4. Row 1: a = 0101, b = 0110. Row 2: a = 01xz, b = 0110 (x ^ 1 and z ^ 0 are
-- x; x & 1 is x; z & 0 is 0).
#guard (match run2 (ha.sem 4) σ_src 1000
    [[("a", .ofNat 4 5), ("b", .ofNat 4 6)], [("a", ⟨#[.lz, .lx, .l1, .l0]⟩), ("b", .ofNat 4 6)]] with
  | .ok [st1, st2] =>
      (SvState.lookup st1 "s").map LVec.toBinString == some "0011" &&
      (SvState.lookup st1 "c").map LVec.toBinString == some "0100" &&
      (SvState.lookup st2 "s").map LVec.toBinString == some "00xx" &&
      (SvState.lookup st2 "c").map LVec.toBinString == some "01x0"
  | _ => false)

/-- A signal whose `W` bits are all known holds the bit vector of its Boolean bits. -/
theorem lookup_bv {st : SvState} {n : String} {W : Nat}
    (hk : ∀ k, k < W → (∃ v, SvState.lookup st n = some v ∧ v.width = W) ∧ KnownBit st n k) (hW : 0 < W) :
    SvState.lookup st n = some (LVec.ofBitVec (XF.bv W (st.boolAt n))) := by
  obtain ⟨⟨v, hv, hvw⟩, -⟩ := hk 0 hW
  have := SvState.lookup_eq_ofBitVec_bv hv hvw (fun k hk' => (hk k hk').2)
  rw [hv, this]

/-- **The contract**, at every width `W ≥ 1` in the `int` range: in every snapshot of every run (every schedule,
every stimulus) in which `a` and `b` hold known values `u`, `v`, the outputs hold `u ^ v` and `u & v`. A snapshot in
which an input has an x or z bit is not constrained by this statement. -/
theorem ha_correct (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) :
    ha.sem W ⊨₂ spec2 fun _ tr => ∀ (k : Nat) (st : SvState), tr[k]? = some st →
      ∀ (u v : BitVec W), SvState.lookup st "a" = some (LVec.ofBitVec u) →
        SvState.lookup st "b" = some (LVec.ofBitVec v) →
        SvState.lookup st "s" = some (LVec.ofBitVec (u ^^^ v)) ∧
          SvState.lookup st "c" = some (LVec.ofBitVec (u &&& v)) := by
  -- 1. structure: every process is combinational, and there is no combinational loop (a rank)
  obtain ⟨hc, hacyc⟩ : CombDesign (ha.sem W) ∧ Acyclic (ha.sem W) := by
    sv_structure (rank := rippleRank (fun p => p) (fun _ _ _ => 0))
    all_goals (intros; omega)
  -- 2. it is enough to look at one settled snapshot
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro u v hA hB
  -- 3. the design's equations, bit by bit (put `trace_state` after this line to read them)
  sv_equations
  · have hWd : (↑W + -1 : Int).natAbs + 1 = W := by omega
    rw [hWd] at eq_s_1 known_s_1 eq_c_1 known_c_1
    -- 4. the mathematics: each output, bit by bit
    rw [lookup_bv known_s_1 (by omega), lookup_bv known_c_1 (by omega)]
    refine ⟨?_, ?_⟩ <;> congr 2 <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
    · rw [XF.getLsbD_bv hi, eq_s_1 i hi, SvState.boolAt_ofBitVec hA hi, SvState.boolAt_ofBitVec hB hi]; simp
    · rw [XF.getLsbD_bv hi, eq_c_1 i hi, SvState.boolAt_ofBitVec hA hi, SvState.boolAt_ofBitVec hB hi]; simp
  -- 5. side goals: ranges of the parameter, and "this input bit is known"
  all_goals first
    | (intros; omega)
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)

#print axioms ha_correct

end Examples.«system-verilog».first_theorem.half_add_proof
