import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.package_signed_struct_elem_e
/--
error: load_design_sv2: 'Examples/system-verilog/sem2/package_signed_struct_elem_e/package_signed_struct_elem_e.sv.json' REFUSED — our defaults elaboration disagrees with the envelope's `resolved` metadata (Lean vs slang differential):
  localparam 'R': constant function 'f': package aggregate 'signed_struct_elem_pkg::P' in a constant context
  package parameter 'signed_struct_elem_pkg::P' is not bound: PackageParameter:signed-packed-aggregate-element: IEEE 1800-2023 §§6.24.1 and 7.2.1 require sign extension, but the parser envelope does not retain an unambiguous signed aggregate value
-/
#guard_msgs (whitespace := lax) in
load_design_sv2 signedStructElem from
  "Examples/system-verilog/sem2/package_signed_struct_elem_e/package_signed_struct_elem_e.sv.json"
end Examples.«system-verilog».sem2.package_signed_struct_elem_e
