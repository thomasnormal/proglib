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
  match j.getNat? with
  | .ok value => pure value
  | .error _ => .error "Natural number expected"

private def optionalNat (j : Json) : Except String (Option Nat) :=
  match j with
  | .null => pure none
  | _ => some <$> nat j

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
    | .str "Deref" => .ok .deref
    | .str s => .ok (.unsupported s)
    | .obj _ => do
        let (kind, value) ← variant p
        match kind with
        | "Field" => do
            let values ← array value
            match values with
            | [index, width] => pure (.field (← nat index) (← nat width))
            | _ => .error "MIR Field projection must contain index and width"
        | "Downcast" => .map Projection.downcast (nat value)
        | other => pure (.unsupported other)
    | _ => .error "MIR place projection must be structured"
  pure { localId, projection }

private def constantProvenance (constant : Json) : Option Nat :=
  match constant.getObjVal? "kind" with
  | .ok (.obj fields) =>
      match fields.toList with
      | [("Allocated", allocated)] =>
          match allocated.getObjVal? "provenance" with
          | .ok provenance =>
              match provenance.getObjVal? "ptrs" with
              | .ok ptrs =>
                  match array ptrs with
                  | .ok (ptr :: _) =>
                      match array ptr with
                      | .ok (_ :: target :: _) => (nat target).toOption
                      | _ => none
                  | _ => none
              | _ => none
          | _ => none
      | _ => none
  | _ => none

private def natFlexible (j : Json) : Except String Nat :=
  match nat j with
  | .ok value => pure value
  | .error _ => do
      let text ← string j
      match text.toNat? with
      | some value => pure value
      | none => .error "Natural number expected"

private def bytesToNat : List Nat → Nat → Nat
  | [], _ => 0
  | byte :: rest, shift => byte * 256 ^ shift + bytesToNat rest (shift + 1)

private def allocationBytes (j : Json) : Except String (List Nat × Bool) := do
  let values ← field j "bytes" >>= array
  values.foldlM (init := ([], true)) fun (bytes, valid) value =>
    match value with
    | .null => pure (bytes ++ [0], false)
    | _ => do
        let byte ← nat value
        pure (bytes ++ [byte], valid)

private def repeatCount (j : Json) : Except String Nat :=
  match nat j with
  | .ok count => pure count
  | .error _ => do
      let kind ← field j "kind"
      let (name, payload) ← variant kind
      if name != "Value" then .error "MIR Repeat count is not a value"
      else
        let values ← array payload
        match values with
        | [_ty, allocation] =>
            let bytes ← field allocation "bytes" >>= array >>= (·.mapM nat)
            pure (bytesToNat bytes 0)
        | _ => .error "MIR Repeat count value is malformed"

private def castKind (j : Json) : Except String CastKind :=
  match j with
  | .str "IntToInt" => pure .intToInt
  | .str "PtrToPtr" => pure .ptrToPtr
  | .str name => pure (.unsupported name)
  | .obj _ => do
      let (name, payload) ← variant j
      match payload with
      | .str detail => pure (.unsupported (name ++ "::" ++ detail))
      | _ => pure (.unsupported name)
  | _ => .error "MIR Cast kind is malformed"

private def operand (j : Json) : Except String Operand := do
  let (kind, value) ← variant j
  match kind with
  | "Copy" => .map Operand.copy (place value)
  | "Move" => .map Operand.move (place value)
  | "Constant" => do
      let constant ← field value "const_"
      let id ← field constant "id" >>= nat
      let ty ← field constant "ty" >>= nat
      match constant.getObjVal? "kind" with
      | .ok (.obj fields) =>
          match fields.toList with
          | [("Allocated", allocated)] =>
              let bytes ← field allocated "bytes" >>= array >>= (·.mapM nat)
              let provenance := constantProvenance constant
              pure (.constant id bytes ty provenance false)
          | [("ZeroSized", _)] => pure (.constant id [] ty none true)
          | _ => pure (.unsupported "Constant kind")
      | .ok (.str "ZeroSized") => pure (.constant id [] ty none true)
      | .ok _ | .error _ => pure (.unsupported "Constant kind")
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
      | ["Ne", left, right] => pure (.binaryNe (← operand left) (← operand right))
      | ["BitAnd", left, right] => pure (.binaryBitAnd (← operand left) (← operand right))
      | ["Div", left, right] => pure (.binaryDiv (← operand left) (← operand right))
      | ["Rem", left, right] => pure (.binaryRem (← operand left) (← operand right))
      | _ => pure (.unsupported "BinaryOp")
  | "CheckedBinaryOp" => do
      let values ← array value
      match values with
      | [op, left, right] => do
          let opName ← string op
          pure (.checkedBinary opName (← operand left) (← operand right))
      | _ => .error "MIR CheckedBinaryOp has malformed operands"
  | "Ref" => do
      let values ← array value
      match values with
      | [_kind, _borrow, placeJson] => .map Rvalue.ref (place placeJson)
      | _ => .error "MIR Ref rvalue has malformed operands"
  | "Aggregate" => do
      let values ← array value
      match values with
      | [tag, operands] => do
          let args ← array operands >>= (·.mapM operand)
          let tagName ←
            match tag with
            | .str name => pure name
            | .obj _ => pure "Adt"
            | _ => .error "MIR Aggregate tag is malformed"
          if args.isEmpty && tagName == "Adt" then
            match tag with
            | .obj _ =>
                let (_, payload) ← variant tag
                match payload with
                | .arr values =>
                    match values.toList.drop 1 |>.head? with
                    | some (.num value) =>
                        if value == 0 then pure .zstAggregate
                        else pure (.unsupported "fieldless Aggregate")
                    | _ => pure (.unsupported "fieldless Aggregate")
                | _ => pure (.unsupported "fieldless Aggregate")
            | _ => pure (.unsupported "fieldless Aggregate")
          else pure (.aggregate tagName args)
      | _ => .error "MIR Aggregate has malformed operands"
  | "Repeat" => do
      let values ← array value
      match values with
      | [operandJson, count] => pure (.repeat (← operand operandJson) (← repeatCount count))
      | _ => .error "MIR Repeat has malformed operands"
  | "Cast" => do
      let values ← array value
      match values with
      | [kind, operandJson, target] =>
          pure (.cast (← castKind kind) (← operand operandJson) (← nat target))
      | _ => .error "MIR Cast has malformed operands"
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
          let target ← field value "target" >>= optionalNat
          let unwind ← field value "unwind"
          let unwindName ←
            match unwind with
            | .str name => pure name
            | _ => (variant unwind).map Prod.fst
          if unwindName == "Continue" then pure (.call func args destination target)
          else pure (.unsupported "Call with cleanup unwind")
      | "Drop" => do
          let place ← field value "place" >>= place
          let target ← field value "target" >>= nat
          let unwind ← field value "unwind"
          let cleanup ←
            match unwind with
            | .obj _ => do
                let (name, payload) ← variant unwind
                if name == "Cleanup" then nat payload else pure target
            | _ => pure target
          pure (.drop place target cleanup)
      | "Resume" => pure .resume
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

private def signedField (shape : Json) : Option Bool :=
  match shape.getObjVal? "value_repr" with
  | .ok repr =>
      match variant repr with
      | .ok ("Scalar", scalar) =>
          match scalar.getObjVal? "Initialized" with
          | .ok initialized =>
              match initialized.getObjVal? "value" with
              | .ok value =>
                  match value.getObjVal? "Int" with
                  | .ok intValue =>
                      match intValue.getObjVal? "signed" with
                      | .ok (.bool signed) => some signed
                      | _ => none
                  | _ => none
              | _ => none
          | _ => none
      | _ => none
  | _ => none

private def typeLayout (j : Json) : Except String TypeLayout := do
  let id ← field j "handle" >>= string
  let kind ← field j "kind" >>= string
  let pointee :=
    match j.getObjVal? "pointee" with
    | .ok (.str value) => value.toNat?
    | _ => none
  let layout ←
    match ← field j "layout" with
    | layout =>
        match layout.getObjVal? "shape" with
        | .ok shape =>
            let sizeBits := match shape.getObjVal? "size" with
              | .ok size => (field size "num_bits" >>= nat).toOption
              | .error _ => none
            let align := match shape.getObjVal? "abi_align" with
              | .ok value => (nat value).toOption
              | .error _ => none
            pure (some (sizeBits, align, signedField shape))
        | .error _ => pure none
  match layout with
  | some (sizeBits, align, signed) => pure { id, kind, pointee, sizeBits, align, signed }
  | none => pure { id, kind, pointee, sizeBits := none, align := none, signed := none }

private def allocation (j : Json) : Except String Allocation := do
  let id ← field j "id" >>= string
  let (bytes, bytesValid) ← allocationBytes j
  let align ← field j "align" >>= nat
  let provenance ←
    match j.getObjVal? "provenance" with
    | .error _ => pure []
    | .ok p =>
        match p.getObjVal? "ptrs" with
        | .error _ => pure []
        | .ok ptrs => array ptrs >>= (·.mapM fun ptr => do
            let values ← array ptr
            match values with
            | [offset, target] => do
                let targetId ←
                  match nat target with
                  | .ok value => pure value
                  | .error _ => field target "allocation" >>= natFlexible
                pure (← nat offset, targetId)
            | _ => .error "allocation provenance entry must contain offset and target")
  pure { id, bytes, bytesValid, provenance, align }

private def allocationIndex : List Allocation → String → Option Nat
  | [], _ => none
  | allocation :: rest, id =>
      if allocation.id == id then some 0
      else allocationIndex rest id |>.map (· + 1)

private def provenanceMap (j : Json) (allocations : List Allocation) : Except String (List (Nat × Nat)) := do
  let values ← array j
  values.foldlM (init := []) fun result item => do
    let kind ← field item "kind" >>= string
    if kind != "memory" then pure result
    else
      let raw ← field item "id" >>= natFlexible
      let allocationId ← field item "allocation" >>= string
      match allocationIndex allocations allocationId with
      | some index => pure ((raw, index) :: result)
      | none => .error "global memory allocation is missing from the allocation table"

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
        let callee ←
          match ← field callJson "callee" with
          | .null => pure none
          | value => some <$> string value
        let resolved ← field callJson "resolved" >>= Lean.Json.getBool?
        pure { caller, block, callee, resolved })
  let types ←
    match j.getObjVal? "tables" with
    | .error _ => pure []
    | .ok tables =>
        match tables.getObjVal? "types" with
        | .error _ => pure []
        | .ok values => array values >>= (·.mapM typeLayout)
  let allocations ←
    match j.getObjVal? "tables" with
    | .error _ => pure []
    | .ok tables =>
        match tables.getObjVal? "allocations" with
        | .error _ => pure []
        | .ok values => array values >>= (·.mapM allocation)
  let provenance ←
    match j.getObjVal? "tables" with
    | .error _ => pure []
    | .ok tables =>
        match tables.getObjVal? "globals" with
        | .error _ => pure []
        | .ok values => provenanceMap values allocations
  pure { schema, entry, bodies, calls, types, allocations, provenance }

def parseEnvelopeString (s : String) : Except String Envelope := do
  let json ← Json.parse s
  parseEnvelope json

end LeanModels.Rust
