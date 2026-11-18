import LeanModels.Rust.Json

namespace LeanModels.Rust

def acceptedSchema : String := "lean-surfaces.rust.mir.v0"

open Lean Elab Command in
elab "load_rust_program " name:ident " from " path:str : command => do
  let pathStr := path.getString
  let contents ←
    match ← (IO.FS.readFile ⟨pathStr⟩).toBaseIO with
    | .ok c => pure c
    | .error e =>
        throwErrorAt path s!"load_rust_program: cannot read '{pathStr}': {e}"
  let envl ←
    match parseEnvelopeString contents with
    | .error e => throwErrorAt path s!"load_rust_program: '{pathStr}' is not a valid MIR envelope: {e}"
    | .ok envl => pure envl
  unless envl.schema == acceptedSchema do
    throwErrorAt path s!"load_rust_program: '{pathStr}' has schema '{envl.schema}', expected '{acceptedSchema}'"
  let declName := (← getCurrNamespace) ++ name.getId
  if (← getEnv).contains declName then
    throwErrorAt name s!"load_rust_program: '{declName}' has already been declared"
  liftCoreM do
    addAndCompile <| .defnDecl {
      name := declName
      levelParams := []
      type := Lean.mkConst ``LeanModels.Rust.Envelope
      value := Lean.toExpr envl
      hints := .abbrev
      safety := .safe }
    enableRealizationsForConst declName
    addDocStringCore declName
      s!"Rust MIR envelope loaded by load_rust_program from '{pathStr}' as a literal Envelope."
  liftTermElabM do
    Term.addTermInfo' name (Lean.mkConst declName) (isBinder := true)

end LeanModels.Rust
