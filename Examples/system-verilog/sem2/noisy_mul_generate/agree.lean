import LeanModels.Sv.Ingest2
import LeanModels.Sv.DesignLemmas
import LeanModels.Sv.CombHier
open LeanModels.Sv
open LeanModels.Sv.Kernel
namespace Examples.«system-verilog».sem2.noisy_mul_generate
load_design_sv2 noisyMul from "Examples/system-verilog/sem2/noisy_mul_generate/noisy_mul_generate.sv.json"
#guard (noisyMul.sem 2).decls.size > 0
#guard (noisyMul.sem 3).decls.size > (noisyMul.sem 2).decls.size
#guard (noisyMul.sem 2).processes.size > 0
#guard match CombHier.summaryH noisyMul.pdesign noisyMul.plib with
  | .error _ => true
  | .ok _ => false
end Examples.«system-verilog».sem2.noisy_mul_generate
#check generated_child_family
#check generated_child_at_prefix
#check generated_child_nested_family

namespace Examples.«system-verilog».sem2.noisy_mul_generate

def andInst : PInst :=
  { name := "u_and", module := "and2f",
    path := [{ label := "g_pp", genvar := some "i" },
      { label := "g_pp_j", genvar := some "j" }],
    conns :=
      [.input "a" (some (.bitSel (.ident "a") (.genvarRef "j"))) false,
       .input "b" (some (.bitSel (.ident "b") (.genvarRef "i"))) false,
       .input "f" (some (.arrayElem "f" [.genvarRef "i", .genvarRef "j"])) false,
       .output "y" (some (.arrayElem "pp" [.genvarRef "i", .genvarRef "j"]))] }

def ppGen : GenItem :=
  .genFor (some "g_pp") "i" (.int 0)
    (.binary .slt (.genvarRef "i") (.paramRef "N" none))
    (.unary .inc (.genvarRef "i")) (some 4)
    [.genFor (some "g_pp_j") "j" (.int 0)
      (.binary .slt (.genvarRef "j") (.paramRef "N" none))
      (.unary .inc (.genvarRef "j")) (some 4) [.inst andInst]]

theorem noisy_pp_generate : noisyMul.pdesign.generates.head? = some ppGen := by
  rfl

theorem andInst_prefix (env : IEnv) (i j : Int) :
    andInst.prefix ((env.bindVal "i" i).bindVal "j" j) =
      .ok ("g_pp[" ++ toString i ++ "].g_pp_j[" ++ toString j ++ "].u_and.") := by
  simpa [andInst, String.append_assoc] using
    (generated_child_prefix_two env andInst "i" "j" "g_pp" "g_pp_j" i j
      (by decide) rfl)

end Examples.«system-verilog».sem2.noisy_mul_generate
