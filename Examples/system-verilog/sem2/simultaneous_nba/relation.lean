import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.NdStep

open LeanModels.Sv LeanModels.Sv.Kernel
namespace Examples.«system-verilog».sem2.simultaneous_nba

/-! The concrete row below instantiates the per-read x rule.  The source has
an unknown start value for `a`, so two executions of the same one-bit `if`
ask the oracle twice and may choose opposite branches.  This is the small
T4c witness currently supported by the relation. -/

load_design_sv2 sn from "Examples/system-verilog/sem2/simultaneous_nba/simultaneous_nba.sv.json"
def E : CoreMemDesign := match sn.e with | .ok d => d | _ => default

def yes : PStmt := .nbaAssign "a" (.int 1)
def no : Option PStmt := some (.nbaAssign "a" (.int 0))

#guard (E.evalExprLocals E.env E.elems E.initial (some 1) [] (.ident "a") ==
  .ok ⟨#[Logic.lx]⟩)

theorem x_read_twice_can_differ
    (h : E.evalExprLocals E.env E.elems E.initial (some 1) [] (.ident "a") =
      .ok ⟨#[Logic.lx]⟩) (o : Oracle) :
    ndOpenStmt E E.initial [] (Oracle.cons true (Oracle.cons false o)) E.env
        (.ifStmt (.ident "a") yes no) =
      .ok (.idle E.initial [], [EdgeWork.edgeStmt E.env yes], Oracle.cons false o) ∧
    ndOpenStmt E E.initial [] (Oracle.cons false o) E.env
        (.ifStmt (.ident "a") yes no) =
      .ok (.idle E.initial [], [EdgeWork.edgeStmt E.env (.nbaAssign "a" (.int 0))], o) := by
  exact ndOpenStmt_if_unknown_twice E E.initial [] E.env (.ident "a") yes no
    h (by rfl) o

#print axioms x_read_twice_can_differ
end Examples.«system-verilog».sem2.simultaneous_nba
