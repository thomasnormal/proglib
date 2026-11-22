import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.HierarchyCoreMem

namespace Examples.«system-verilog».seq_neg.signed_child_param_check

open LeanModels.Sv
open LeanModels.Sv.Kernel

/-! A signed four-bit child parameter read directly into a 64-bit output is
sign-extended by both pinned simulators.  Icarus Verilog 13.0 and Xcelium
24.03-s004 each print `fffffffffffffff8`.  The direct canonical-E row agrees.
The hierarchy substitution helper separately refuses the signed narrow value
until it has a sign-preserving representation. -/
load_design_sv2 signedParent from
  "Examples/system-verilog/seq_neg/signed_child_param.sv.json"

#guard (signedParent.sem 8).processes.size == 2
#guard match signedParent.e 8 with
  | .ok d => d.processes.toList.any fun p =>
      match p with
      | .assign _ (.unsupported "ParamRef:signed-width" _) => true
      | _ => false
  | _ => false
#guard match run2 (signedParent.sem 8) σ_src 1000 [[]] with
  | .ok [st] => (SvState.lookup st "value").map LVec.toBinString ==
      some "1111111111111111111111111111111111111111111111111111111111111000"
  | _ => false

#check hParamVals_signed_narrow_refusal
#check hParamVals_int_binding
#print axioms hParamVals_signed_narrow_refusal
#print axioms hParamVals_int_binding

end Examples.«system-verilog».seq_neg.signed_child_param_check
