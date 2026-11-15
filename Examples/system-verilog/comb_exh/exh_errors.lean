import LeanModels.Sv.Ingest2
import LeanModels.Sv.CombExhaustiveTactic
import Examples.«system-verilog».comb_exh.statement

/-!
# `sv_exhaustive` on a wrong table: refused, naming the input and the bit (comb_exh)

`comb_exh_bad.sv` is the table of `comb_exh_table.sv` with one wrong item (`4'd11: y = 3'd2`, where 11 has three ones).
`sv_exhaustive` gets through the design's structure and the compiled program and then fails the exhaustive decision of
`y`; it reports the first input at which the netlist and the task differ and the first differing bit. The task is the
one of `exh_proof.lean`, restated here (the two files are independent tests).
-/

namespace Examples.«system-verilog».comb_exh.exh_errors

open LeanModels.Sv
open Examples.«system-verilog».comb_exh.statement

load_design_sv2 comb_exh_bad from "Examples/system-verilog/comb_exh/comb_exh_bad.sv.json"

/-- The number of ones of a 4-bit vector, counted bit by bit. -/
def pop4 (x : BitVec 4) : BitVec 3 :=
  BitVec.ofNat 3 ((List.range 4).countP fun i => x.getLsbD i)

/-- The table task of `exh_proof.lean`. -/
def popTask : SvGolf.CombTask where
  inRange N := N = 0
  inputs _ := [("x", 4)]
  outputs _ := [("y", 3)]
  fn _ := fun (x, ()) => (pop4 x, ())

/--
error: sv_exhaustive: output `y` differs at inputs [(x, 11)]: the netlist gives 2, the task 3; first differing bit y[0]
-/
#guard_msgs (whitespace := lax) in
example : popTask.StatementFixed comb_exh_bad.sem := by
  sv_exhaustive

end Examples.«system-verilog».comb_exh.exh_errors
