import LeanModels.Python.Machine.Core
import LeanModels.Python.Machine.Relation

namespace LeanModels.Python.Machine

/-! Kernel checks for the first machine slice. -/

private def span : LeanModels.Span :=
  { lineno := 1, colOffset := 0, endLineno := 1, endColOffset := 1 }

private def toy : Module where
  functions := #[]
  topLevel := #[.ret (some (.constant (.int 7) span)) span]

private def printing : Module where
  functions := #[]
  topLevel := #[.exprStmt (.call (.name "print" span) #[.constant (.str "hello") span] #[] none span) span]

private def failing : Module where
  functions := #[]
  topLevel := #[.exprStmt (.name "missing" span) span]

private def refusing : Module where
  functions := #[]
  topLevel := #[.unsupported "ClassDef" "class C: pass" span]

#guard (initial toy).frames.length == 1
#guard (run Impl.cpython39 8 toy).2 == .returned (.int 7)
#guard (run Impl.cpython39 8 printing).1.events == [.output "hello", .return .none]
#guard (run Impl.cpython39 8 failing).2 == .raised (.nameError "missing")
#guard (run Impl.cpython39 8 refusing).2 == .refused "machine statement"
#guard (run Impl.cpython39 0 toy).2 == .resource .recursion

example : (run Impl.cpython39 8 toy).2 = .returned (.int 7) := by
  rfl

end LeanModels.Python.Machine
