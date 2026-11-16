import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.child_instance_wall.agree

/- The missing child is deliberate.  The collect-all census records the
parser-native `UninstantiatedDefSymbol:UninstantiatedDef` and the frontend's
`SlangError:UnknownModule`; no simulator result is claimed for an unresolved
module definition. -/
load_design_sv2 childInstanceWall from
  "Examples/system-verilog/sem2/child_instance_wall/child_instance_wall.sv.json"

end Examples.«system-verilog».sem2.child_instance_wall.agree
