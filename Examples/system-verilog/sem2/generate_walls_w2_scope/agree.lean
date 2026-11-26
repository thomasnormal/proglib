/-
Canonical-E receipt for declarations directly inside a generate-for body.
The parser-native declaration `t` is materialized once per generated scope,
so each assignment retains the source-shaped hierarchical name.
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.generate_walls_w2_scope.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 w2Scope from
  "Examples/system-verilog/sem2/generate_walls_w2_scope/w2_scope.json"

#guard match w2Scope.e 2 with
  | .ok d => d.scalar.decls.toList.map (fun (x : Decl) => x.name) ==
      ["a", "q", "g[0].t", "g[1].t"]
  | _ => false

#guard match w2Scope.e 2 with
  | .ok d =>
      match d.processes.toList with
      | [.assign (.ident "g[0].t") (.bitSel (.ident "a") (.int 0)),
         .assign (.bitSel "q" (.int 0)) (.ident "g[0].t"),
         .assign (.ident "g[1].t") (.bitSel (.ident "a") (.int 1)),
         .assign (.bitSel "q" (.int 1)) (.ident "g[1].t")] => true
      | _ => false
  | _ => false

end Examples.«system-verilog».sem2.generate_walls_w2_scope.agree
