import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.nested_generate_template_e
open LeanModels.Sv
load_design_sv2 nestedGenerateTemplate from
  "Examples/system-verilog/sem2/nested_generate_template_e/nested_generate_template_e.sv.json"
#guard nestedGenerateTemplate.pdesign.generates.length == 1
end Examples.«system-verilog».sem2.nested_generate_template_e
