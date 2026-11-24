import LeanModels.Sv.Hier2Gen
import LeanModels.Sv.CombHier
import LeanModels.Sv.CombEBase
import LeanModels.Sv.Comb2Term

/-!
# Reader's index for compositional SystemVerilog design proofs

This module is an index, not a second semantics.  The named lemmas below are
stated over the ordinary source-shaped parameter and `Design2` definitions.
They are the hand-proof entry points used by hierarchy and generate proofs.

* `PDesign.instantiateRec_of_ok` splits one hierarchical instantiation into
  its parameter environment, declarations, elements, and generated processes.
* `GenItem.expandH_genFor_ascending_flatMap` gives one structural induction
  step for an ascending generate-for; `GenItem.expandH_inst` and
  `instExpandH_of` expose one child's flattened declarations and processes.
* `PDesign.assembleH_decls` and `PDesign.assembleH_processes` connect the
  generated pieces back to the ordinary hierarchical design.
* `CombDesign` and `Acyclic` are the profile and dependency contracts for a
  settled combinational design; `CombDesign.of_single` is the base case and
  `Acyclic.of_single` is the corresponding one-process rank case.
* `CombView.comb_of_summary`, `CombView.acyclic_of_summary`, and
  `CombView.acyclic_of_lex` turn a proved source-shaped summary into those
  contracts without introducing a new evaluator.
* `CombHier.instantiateHDAlias2_twin` is the bridge when a module-level
  hierarchy has a flat twin; its hypotheses are the named parameter, width,
  fragment, and child-environment obligations.

A hand proof should use these equations first and only then invoke a tactic as
an optional plumbing layer.  No theorem in this index is bounded by an
executor fuel or by a fixed number of cycles; the `F` arguments in the
instantiation equations are the language's generate-expansion interface and
are discharged by the corresponding structural theorem.
-/

namespace LeanModels.Sv

/-! The declarations above are intentionally the public index.  Keeping this
file import-only makes the index cheap to read and prevents it from becoming a
parallel proof layer. -/

end LeanModels.Sv
