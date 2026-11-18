import Lean
import LeanModels.Rust.Ast

namespace LeanModels.Rust

open Lean (Json)

private def withCtx (ctx : String) (r : Except String α) : Except String α :=
  match r with
  | .ok value => .ok value
  | .error message => .error s!"{ctx}: {message}"

private def field (j : Json) (name : String) : Except String Json :=
  match j.getObjVal? name with
  | .ok value => .ok value
  | .error _ => .error s!"missing object field '{name}'"

private def string (j : Json) : Except String String :=
  j.getStr?

private def nat (j : Json) : Except String Nat :=
  j.getNat?

private def int (j : Json) : Except String Int :=
  j.getInt?

private def array (j : Json) : Except String (List Json) :=
  match j with
  | .arr values => .ok values.toList
  | _ => .error "expected a JSON array"

private def object (j : Json) : Except String (List (String × Json)) :=
  match j with
  | .obj fields => .ok fields.toList
  | _ => .error "expected a JSON object"

private def variant (j : Json) : Except String (String × Json) := do
  let fields ← object j
  match fields with
  | [(name, value)] => .ok (name, value)
  | _ => .error "expected a single-variant MIR object"

private def place (j : Json) : Except String Place := do
  let localId ← field j "local" >>= nat
  let projections ← field j "projection" >>= array
  let projection ← projections.mapM fun p =>
    match p with
    | .str s => .ok s
    | _ => .error "MIR place projection is not a string"
  pure { localId, projection }

private def operand (j : Json) : Except String Operand := do
  let (kind, value) ← variant j
  match kind with
  | "Copy" => .map Operand.copy (place value)
  | "Move" => .map Operand.move (place value)
  | "Constant" => do
      let constant ← field value "const_"
      let id ← field constant "id" >>= nat
      let bytes ←
        match constant.getObjVal? "kind" with
        | .ok (.obj fields) =>
            match fields.toList with
            | [("Allocated", allocated)] => field allocated "bytes" >>= array >>= (·.mapM nat)
            | [("ZeroSized", _)] => pure []
            | _ => pure []
        | .ok _ | .error _ => pure []
      pure (.constant id bytes)
  | other => pure (.unsupported other)

private def rvalue (j : Json) : Except String Rvalue := do
  let (kind, value) ← variant j
  match kind with
  | "Use" => do
      let values ← array value
      match values with
      | operandJson :: _ => .map Rvalue.use (operand operandJson)
      | _ => .error "MIR Use rvalue has no operand"
  | "BinaryOp" => do
      let values ← array value
      match values with
      | ["Eq", left, right] => pure (.binaryEq (← operand left) (← operand right))
      | ["BitAnd", left, right] => pure (.binaryBitAnd (← operand left) (← operand right))
      | ["Div", left, right] => pure (.binaryDiv (← operand left) (← operand right))
      | _ => pure (.unsupported "BinaryOp")
  | other => pure (.unsupported other)

private def statement (j : Json) : Except String Statement := do
  let (kind, value) ← variant j
  match kind with
  | "Assign" => do
      let values ← array value
      match values with
      | [placeJson, rvalueJson] => return .assign (← place placeJson) (← rvalue rvalueJson)
      | _ => .error "MIR Assign does not have two operands"
  | "StorageLive" => .map Statement.storageLive (nat value)
  | "StorageDead" => .map Statement.storageDead (nat value)
  | "PlaceMention" => .map Statement.placeMention (place value)
  | other => pure (.unsupported other)

private def terminator (j : Json) : Except String Terminator := do
  match j with
  | .str "Return" => pure .ret
  | .obj _ => do
      let (kind, value) ← variant j
      match kind with
      | "Return" => pure .ret
      | "Goto" => .map Terminator.goto (field value "target" >>= nat)
      | "SwitchInt" => do
          let discr ← field value "discr" >>= operand
          let targets ← field value "targets"
          let branches ← field targets "branches" >>= array >>= (·.mapM fun branch => do
            let values ← array branch
            match values with
            | [value, target] => pure (← int value, ← nat target)
            | _ => .error "MIR SwitchInt branch must contain a value and target")
          let otherwise ← field targets "otherwise" >>= nat
          pure (.switchInt discr branches otherwise)
      | "Assert" => do
          let cond ← field value "cond" >>= operand
          let expected ← field value "expected" >>= Lean.Json.getBool?
          let target ← field value "target" >>= nat
          let unwind ← field value "unwind"
          let unwindName ←
            match unwind with
            | .str name => pure name
            | _ => (variant unwind).map Prod.fst
          if unwindName == "Continue" then pure (.assert cond expected target)
          else pure (.unsupported "Assert with cleanup unwind")
      | "Call" => do
          let func ← field value "func" >>= operand
          let args ← field value "args" >>= array >>= (·.mapM operand)
          let destination ← field value "destination" >>= place
          let target ← field value "target" >>= nat
          let unwind ← field value "unwind"
          let unwindName ←
            match unwind with
            | .str name => pure name
            | _ => (variant unwind).map Prod.fst
          if unwindName == "Continue" then pure (.call func args destination target)
          else pure (.unsupported "Call with cleanup unwind")
      | "Unreachable" => pure .unreachable
      | other => pure (.unsupported other)
  | .str other => pure (.unsupported other)
  | _ => .error "MIR terminator must be a string or single-variant object"

private def block (j : Json) : Except String Block := do
  let statements ← field j "statements" >>= array >>= (·.mapM fun item =>
    withCtx "statement" (field item "kind" >>= statement))
  let terminatorJson ← field j "terminator"
  pure { statements, terminator := ← withCtx "terminator" (field terminatorJson "kind" >>= terminator) }

private def body (instanceId : String) (j : Json) : Except String Body := do
  let blocks ← field j "blocks" >>= array >>= (·.mapM (withCtx "block" ∘ block))
  pure { instanceId, blocks }

def parseEnvelope (j : Json) : Except String Envelope := do
  let schema ← field j "schema" >>= string
  let entry ← field j "entry" >>= string
  let bodiesJson ← field j "bodies" >>= array
  let bodies ← bodiesJson.mapM fun bodyJson => do
    let instanceId ← field bodyJson "instance" >>= string
    let bodyJson ← field bodyJson "body"
    withCtx "body" (body instanceId bodyJson)
  let calls ←
    match j.getObjVal? "calls" with
    | .error _ => pure []
    | .ok callsJson => array callsJson >>= (·.mapM fun callJson => do
        let caller ← field callJson "caller" >>= string
        let block ← field callJson "block" >>= nat
        let callee ← field callJson "callee" >>= string
        let resolved ← field callJson "resolved" >>= Lean.Json.getBool?
        pure { caller, block, callee, resolved })
  pure { schema, entry, bodies, calls }

def parseEnvelopeString (s : String) : Except String Envelope := do
  let json ← Json.parse s
  parseEnvelope json

end LeanModels.Rust
