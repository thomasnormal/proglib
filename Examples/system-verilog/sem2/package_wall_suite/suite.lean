import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.package_wall_suite

structure Row where
  pack : String
  name : String
  expected : String
  current : String
private def rows : List Row := [
  { pack := "walls-1125b", name := "a0_default_alone", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1125b", name := "a1_default_poison_array", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1125b", name := "a2_default_poison_alias", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1125b", name := "a3_localparam_alone", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1125b", name := "a4_localparam_poison", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1125b", name := "a5_partsel_alone", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1125b", name := "a6_partsel_poison", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1125b", name := "b1_typedef", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1125b", name := "b2_typedef_array", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1125b", name := "c1_chain", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1125b", name := "c2_chain_unused", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1125b", name := "f1_pkg_const_function", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1125b", name := "f2_pkg_struct_function", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1125b", name := "f3_pkg_wide_struct", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1125b", name := "old1_package_parameter", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1125b", name := "old2_package_parameter_chain", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1125b", name := "old3_struct_part_select", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1125b", name := "old4_localparam_generate", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1125b", name := "old5_typed_declaration", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126", name := "h1_procedural_fn", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126", name := "h2_ready_order", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126", name := "h3_nested_call", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126", name := "h3_call_in_arith", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126", name := "h3_direct_call_ok", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126", name := "h4_fn_result_param", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126", name := "h4_fn_result_process", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126", name := "h4_expr_process", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126", name := "r1_port_width", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126", name := "b3_typed_localparam", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126", name := "b3_typed_variable", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126", name := "b4_alias_port", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126", name := "b4_alias_const_use", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126", name := "b5_array_variable", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126", name := "b6_typedef_of_array", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126", name := "m1_module_fn_arg", expected := "source-shaped package wall behavior from packet", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126c/W1", name := "w1a_gfor_fnproc_clog2", expected := "constant-function generate-local evaluation", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126c/W1", name := "w1b_gfor_fnproc_bare", expected := "constant-function generate-local evaluation", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126c/W1", name := "w1c_gfor_fnret_clog2", expected := "constant-function generate-local evaluation", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126c/W1", name := "w1d_gfor_fnret_bare", expected := "constant-function generate-local evaluation", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126c/W1", name := "w1e_gfor_pkgfn_clog2", expected := "constant-function generate-local evaluation", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126c/W1", name := "w1f_gfor_pkgret_clog2", expected := "constant-function generate-local evaluation", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126c/W1", name := "w1g_gfor_clog2_only", expected := "constant-function generate-local evaluation", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126c/W1", name := "w1h_gif_fnproc_clog2", expected := "constant-function generate-local evaluation", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126c/W1", name := "w1i_gfor_fnproc_const", expected := "constant-function generate-local evaluation", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126c/W1", name := "w1j_module_fnproc_clog2", expected := "constant-function generate-local evaluation", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126c/W1", name := "w1k_gfor_fnproc_wide", expected := "constant-function generate-local evaluation", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126c/W1", name := "w1l_gfor_pkgret_bare", expected := "constant-function generate-local evaluation", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126c/W1", name := "w1m_gfor_pkgproc_bare", expected := "constant-function generate-local evaluation", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126c/W1", name := "w1n_module_fnret_clog2", expected := "constant-function generate-local evaluation", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126c/W1", name := "w1o_gif_fnret_bare", expected := "constant-function generate-local evaluation", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126c/W2", name := "w2a_gfor_scalar", expected := "load at N=1; per-instance names at N>=2", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126c/W2", name := "w2b_gfor_vector", expected := "load at N=1; per-instance names at N>=2", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126c/W2", name := "w2c_gfor_unpacked", expected := "load at N=1; per-instance names at N>=2", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126c/W2", name := "w2d_gif_else_same_name", expected := "load at N=1; per-instance names at N>=2", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126c/W2", name := "w2e_two_loops_same_name", expected := "load at N=1; per-instance names at N>=2", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126c/W2", name := "w2f_shadow_module_name", expected := "load at N=1; per-instance names at N>=2", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126c/W2", name := "w2g_gfor_if_decl", expected := "load at N=1; per-instance names at N>=2", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126c/W2", name := "w2h_gfor_no_decl", expected := "load at N=1; per-instance names at N>=2", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126d", name := "implicit_event_loop", expected := "simulator-accepted source-shaped construct", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126d", name := "readmemh_parameter_file", expected := "simulator-accepted source-shaped construct", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126d", name := "inactive_child_definition", expected := "load when inactive; loud refusal when selected", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126e", name := "h4c_unused", expected := "loud width-exact refusal pending helper", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126e", name := "h4c_read", expected := "loud width-exact refusal pending helper", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126e", name := "h4s_unused", expected := "loud width-exact refusal pending helper", current := "known-failing at 2026-11-26 pack baseline" },
  { pack := "walls-1126e", name := "h4s_read", expected := "loud width-exact refusal pending helper", current := "known-failing at 2026-11-26 pack baseline" },
]

#guard rows.length == 65
#guard (rows.map (fun r => r.pack ++ "/" ++ r.name)).eraseDups.length == rows.length
#guard rows.all (fun r => !r.expected.isEmpty && !r.current.isEmpty)
#guard rows.any (fun r => r.pack == "walls-1125b")
#guard rows.any (fun r => r.pack == "walls-1126")
#guard rows.any (fun r => r.pack == "walls-1126c/W1")
#guard rows.any (fun r => r.pack == "walls-1126c/W2")
#guard rows.any (fun r => r.pack == "walls-1126d")
#guard rows.any (fun r => r.pack == "walls-1126e")

end Examples.«system-verilog».sem2.package_wall_suite
