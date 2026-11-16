/-
# Ordinary sv-0.2 refusal census

This runner is deliberately a thin instrument over `load_design_sv2`'s
existing parser and admission functions.  It does not implement a second
SystemVerilog checker: `PDesign.instantiateE2`, `crossCheckFull`, and the
existing semantic guard functions provide the decisions.  A source-shaped
unsupported node is retained and reported so later nodes can still be seen.

Usage:

  lake env lean --run harness/sv/refusal_census.lean design.sv.json

Output is JSON Lines.  Every line has `stage`, `construct`, `line` (null when
the typed PDesign has no source span), `function`, and `message`.
-/

import Lean
import LeanModels.Sv.Ingest2

open Lean (Json)
open LeanModels.Sv
open LeanModels.Sv.Kernel

namespace SvRefusalCensus

structure Row where
  construct : String
  function : String
  message : String
deriving Repr, BEq

def rowJson (r : Row) : Json :=
  Json.mkObj [
    ("stage", Json.str "ordinary"),
    ("construct", Json.str r.construct),
    ("line", Json.null),
    ("function", Json.str r.function),
    ("message", Json.str r.message)]

def exprRows : PExpr → List Row
  | .unsupported k t => [{ construct := k, function := "parsePExpr", message := t }]
  | .unary _ a | .reduce _ a | .cast _ a | .sysCall _ a
  | .resize _ a | .signedResize _ a | .squash2 _ a => exprRows a
  | .binary _ a b | .ternary a b _ => exprRows a ++ exprRows b
  | .concat xs => xs.flatMap exprRows
  | .bitSel a b | .partSel a b _ => exprRows a ++ exprRows b
  | .repl a b => exprRows a ++ exprRows b
  | .arrayElem _ xs => xs.flatMap exprRows
  | .arrayPart _ xs _ a b => xs.flatMap exprRows ++ exprRows a ++ exprRows b
  | .functionCall _ xs => xs.flatMap exprRows
  | _ => []

def lhsRows : PLhs → List Row
  | .concat xs => xs.flatMap lhsRows
  | .bitSel _ i | .partSel _ i _ | .arrayElem _ [i] => exprRows i
  | .arrayElem _ xs | .arrayPart _ xs .. => xs.flatMap exprRows
  | _ => []

partial def stmtRows : PStmt → List Row
  | .blockingAssign _ e | .nbaAssign _ e => exprRows e
  | .blockingAssignL l e | .nbaAssignL l e => lhsRows l ++ exprRows e
  | .ifStmt c t e => exprRows c ++ stmtRows t ++ e.toList.flatMap stmtRows
  | .block xs => xs.flatMap stmtRows
  | .forLoop _ a b c body => exprRows a ++ exprRows b ++ exprRows c ++ stmtRows body
  | .caseStmt s items d _ _ =>
      exprRows s ++ items.flatMap (fun (ps, b) => ps.flatMap exprRows ++ stmtRows b) ++
        d.toList.flatMap stmtRows
  | .unsupported k t => [{ construct := k, function := "parsePStmt", message := t }]

def processRows : PProcess → List Row
  | .alwaysFF _ b | .alwaysPlain _ b | .alwaysComb b | .alwaysImplicit b
  | .alwaysFFR _ _ b _ | .initial b => stmtRows b
  | .assign _ e | .assignL _ e => exprRows e
  | .unsupported k t => [{ construct := k, function := "parsePProcess", message := t }]

def genRows : GenItem → List Row
  | .process p => processRows p
  | .decl _ => []
  | .genFor _ _ a b c _ body => exprRows a ++ exprRows b ++ exprRows c ++ body.flatMap genRows
  | .genIf c t e => exprRows c ++ t.flatMap genRows ++ e.flatMap genRows
  | .unsupported k t => [{ construct := k, function := "GenItem.expand", message := t }]
  | .inst i => i.conns.flatMap fun c => match c with
      | .unsupported _ k t => [{ construct := k, function := "parsePConn", message := t }]
      | .input _ e _ => e.toList.flatMap exprRows
      | .output _ l => l.toList.flatMap lhsRows

def designRows (d : PDesign) : List Row :=
  d.processes.flatMap processRows ++ d.generates.flatMap genRows ++
    d.others.map fun (k, t) => { construct := k, function := "PDesign.instantiate", message := t }

def guardRows (pd : PDesign) (lib : List PDesign) : List Row :=
  let cross := (pd.crossCheckFull.1.map fun m =>
    { construct := "cross-check", function := "PDesign.crossCheckFull", message := m })
  let libs := lib.flatMap fun c => c.crossCheck.map fun m =>
    { construct := "cross-check", function := "PDesign.crossCheck", message := s!"{c.name}: {m}" }
  let point := match pd.atPoint [] with
    | .error e => [{ construct := "parameter-point", function := "PDesign.atPoint", message := e }]
    | .ok (p, args) =>
        let i32 := if lib.isEmpty then p.int32Agrees args else p.int32AgreesH lib args
        (if i32 then [] else [{ construct := "Constant:int32", function := "PDesign.int32Agrees", message := "default point leaves the exact 32-bit int tier" }])
  cross ++ libs ++ point

def canonicalERows (d : CoreMemDesign) : List Row :=
  d.processes.toList.flatMap fun p =>
    match p with
    | .unsupported k t =>
        [{ construct := k, function := "PDesign.instantiateE2", message := t }]
    | _ => []

def eRows (envl : Envelope2) : List Row :=
  let pd := envl.design
  let args := pd.defaultArgs.toOption.getD []
  let clock := pd.clockReport envl.lib args
  let clockRows := match clock with
    | none => []
    | some (kind, message) => [{ construct := kind, function := "PDesign.clockReport", message }]
  let r := if envl.lib.isEmpty then
      LeanModels.Sv.Kernel.PDesign.instantiateE2 pd args (PDesign.surfaceFuel args)
    else
      LeanModels.Sv.Kernel.PDesign.instantiateE2H pd envl.lib args
  clockRows ++ match r with
    | .ok d => canonicalERows d
    | .timeout => [{ construct := "Instantiation:E:timeout", function := "PDesign.instantiateE2", message := "generate expansion fuel exhausted" }]
    | .unsupported m => [{ construct := "Instantiation:E:unsupported", function := "PDesign.instantiateE2", message := m }]

def collect (envl : Envelope2) : List Row :=
  let pd := envl.design
  let lib := envl.lib
  (designRows pd ++ guardRows pd lib ++ eRows envl).eraseDups

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
      let text ← IO.FS.readFile path
      match parseEnvelope2String text with
      | .error e =>
          IO.println (rowJson { construct := "Envelope", function := "parseEnvelope2String", message := e } |>.compress)
          return 1
      | .ok envl =>
          for row in collect envl do IO.println (rowJson row |>.compress)
          return 0
  | _ =>
      IO.eprintln "usage: lake env lean --run harness/sv/refusal_census.lean <design.sv.json>"
      return 2

end SvRefusalCensus

def main := SvRefusalCensus.main
