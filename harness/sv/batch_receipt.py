#!/usr/bin/env python3
"""Run one seeded ordinary-E/source differential pass over the clean-room rows.

The manifest is deliberately explicit: the SystemVerilog frontend remains the
only source parser, while this script only describes the ports needed to drive
the parser-produced design.  A temporary Lean program loads every envelope
through ``load_design_sv2`` and executes ``CoreMemDesign``.  The same stimulus
is emitted into a generated source testbench for Icarus and Xcelium.

Run from the repository root, for example::

    python3 harness/sv/batch_receipt.py --cleanroom-dir /path/to/cleanroom

The command prints one ``CYCLE`` line per simulator and fixture, followed by a
per-cycle MATCH/DIVERGE verdict.  No generated source, envelope, simulator
work library, or Lean file is written into the repository.
"""

from __future__ import annotations

import argparse
import os
import random
import re
import shutil
import signal
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
EXTRACT = ROOT / "extractors" / "sv" / "extract.py"
SEED = 0x5EED_2026
CYCLES = 8


@dataclass(frozen=True)
class Port:
    name: str
    width: int
    clock: bool = False
    reset_active_low: bool = False


@dataclass(frozen=True)
class Point:
    label: str
    args: tuple[int, ...]
    # Some source-level checks deliberately terminate Xcelium with a
    # diagnostic after producing the requested rows.  Keep that diagnostic
    # explicit and accept it only when every marker is present.
    expected_simulator_diagnostics: tuple[str, ...] = ()


@dataclass(frozen=True)
class Fixture:
    source: str
    top: str
    inputs: tuple[Port, ...]
    outputs: tuple[Port, ...]
    points: tuple[Point, ...] = (Point("default", ()),)
    retain_loops: bool = False
    retain_proc_rewrites: bool = False
    # Expected ordinary-route refusal substring for a clean-room boundary.
    # An empty value means the fixture must run eight E cycles.
    expected_ordinary_refusal: str = ""
    # Expected refusal from the ordinary loader/cross-check before a design
    # family can be elaborated.  These fixtures are measured by refusal_census
    # and still receive both pinned source-simulator rows.
    expected_loader_refusal: str = ""
    # A legal source construct may be rejected by one pinned simulator's
    # frontend.  A refusal receipt records that outcome explicitly; it is
    # never treated as an oracle match.
    expected_source_refusals: tuple[str, ...] = ()


# This is the bounded runnable set from the ordinary-route census.  Widths are
# source facts, not a second parser: Slang still produces and validates each
# envelope before Lean or a simulator sees it.
FIXTURES: tuple[Fixture, ...] = (
    # The inbox order starts with the storage/index walls that external users
    # are waiting on, then the variable-index loop, explicit width conversion,
    # and packed-register family.  The remaining runnable census rows follow.
    Fixture("parameterized_unpacked_storage.sv", "parameterized_unpacked_storage",
            (Port("x", 8),), (Port("y", 8),),
            (Point("N1", (1,)), Point("N2", (2,)))),
    Fixture("default_point_array.sv", "default_point_array",
            (Port("clk", 1, clock=True), Port("d", 8)), (Port("q", 8),),
            retain_loops=True, retain_proc_rewrites=True),
    Fixture("generated_array_index.sv", "generated_array_index",
            (Port("x", 8),), (Port("y", 8),),
            retain_proc_rewrites=True),
    Fixture("generated_array_nested.sv", "generated_array_nested",
            (Port("x", 8), Port("taps", 8)), (Port("y", 8),),
            (Point("W4", (4,)), Point("W8", (8,))),
            retain_proc_rewrites=True),
    Fixture("generate_if_unpacked_array.sv", "generate_if_unpacked_array",
            (Port("x", 8),), (Port("y", 8),),
            (Point("N1", (1,)), Point("N2", (2,))),
            retain_proc_rewrites=True),
    Fixture("unpacked_generate_array.sv", "unpacked_storage",
            (Port("x", 8),), (Port("y", 8),),
            retain_proc_rewrites=True),
    Fixture("unpacked_array_target.sv", "unpacked_array_target",
            (Port("x", 8), Port("idx", 1)), (Port("y", 8),),
            retain_proc_rewrites=True),
    Fixture("for_loop.sv", "for_loop",
            (Port("clk", 1, clock=True), Port("d", 8)), (Port("q", 8),),
            retain_loops=True, retain_proc_rewrites=True),
    Fixture("parameterized_size_cast.sv", "parameterized_size_cast_canonical_e",
            (Port("x", 8),), (Port("y", 2),),
            (Point("W2", (2,)), Point("W12", (12,)))),
    Fixture("packed_shift_register.sv", "packed_shift_register_canonical_e",
            (Port("clk", 1, clock=True), Port("v", 1)), (Port("q", 4),),
            (Point("N4", (4,)), Point("N8", (8,)))),
    Fixture("constant_width_conversion.sv", "constant_width_conversion",
            (Port("x", 1),), (Port("y", 1),),
            (Point("E8", (8,)), Point("E4", (4,)))),
    Fixture("localparam_shift.sv", "localparam_shift",
            (Port("x", 8),), (Port("y", 8),),
            (Point("E8", (8,)), Point("E4", (4,)))),
    Fixture("array_index.sv", "array_index",
            (Port("i", 2),), (Port("y", 8),)),
    Fixture("memory_edge_loop.sv", "memory_edge_loop",
            (Port("clk", 1, clock=True), Port("d", 8)), (Port("q", 8),),
            (Point("default", ()),),
            retain_loops=True, retain_proc_rewrites=True),
    Fixture("function_source_edge.sv", "function_source_edge",
            (Port("clk", 1, clock=True), Port("d", 1)), (Port("q", 1),),
            retain_proc_rewrites=True),
    Fixture("automatic_function_subroutine.sv", "automatic_function_subroutine",
            (Port("clk", 1, clock=True), Port("d", 1)), (Port("q", 1),),
            retain_proc_rewrites=True),
    Fixture("function_generated_large_case.sv", "function_call",
            (Port("a", 8),), (Port("y", 8),),
            retain_proc_rewrites=True),
    Fixture("function_unique_local_case.sv", "function_unique_local_case",
            (Port("a", 5),), (Port("y", 5),),
            retain_proc_rewrites=True),
    Fixture("package_function_case.sv", "package_function_case",
            (Port("a", 5),), (Port("y", 5),),
            retain_proc_rewrites=True),
    Fixture("constant_function_child.sv", "constant_function_top",
            (Port("x", 4),), (Port("y", 2),),
            (Point("N1", (1,)), Point("N4", (4,))),
            retain_proc_rewrites=True),
    Fixture("generate_local_hierarchy.sv", "generate_local_top",
            (Port("x", 4),), (Port("y", 4),),
            (Point("N1", (1,)), Point("N4", (4,))),
            retain_proc_rewrites=True),
    Fixture("proc_local_automatic.sv", "proc_local_automatic",
            (Port("clk", 1, clock=True), Port("a", 8)), (Port("y", 8),),
            retain_proc_rewrites=True,
            expected_ordinary_refusal="LocalDecl",
            expected_source_refusals=("iverilog",)),
    Fixture("proc_local_static_e.sv", "proc_local_static_e",
            (Port("clk", 1, clock=True), Port("a", 8)), (Port("y", 8),)),
    Fixture("proc_local_static_init_e.sv", "proc_local_static_init_e",
            (Port("clk", 1, clock=True), Port("en", 1), Port("a", 8)),
            (Port("y", 8),), expected_source_refusals=("xrun",)),
    Fixture("event_always_repro.sv", "event_always_repro",
            (Port("clk", 1, clock=True), Port("d", 1)), (Port("q", 1),),
            expected_ordinary_refusal="TimedStatement:DelayControl"),
    Fixture("proc_local_for_automatic.sv", "proc_local_for_automatic",
            (Port("a", 8),), (Port("y", 8),),
            points=(Point("N8", (8,)),),
            expected_ordinary_refusal="ForLoop",
            expected_source_refusals=()),
    Fixture("darkriscv_nonliteral_initializer.sv", "nonliteral_initializer",
            (Port("a", 1),), (Port("q", 2),),
            expected_ordinary_refusal="non-literal initializer"),
    Fixture("packed_enum_dimension.sv", "packed_enum_dimension",
            (Port("mode", 2),), (Port("y", 1),),
            retain_proc_rewrites=True),
    Fixture("packed_enum_dimension_repro.sv", "packed_enum_dimension_repro",
            (Port("raw", 2),), (Port("y", 1),),
            (Point("W2", (2,)), Point("W4", (4,))),
            expected_loader_refusal="EnumValueSymbol:unsized-literal-member"),
    Fixture("generate_parameter.sv", "generate_parameter",
            (Port("x", 1),), (Port("y", 1),),
            (Point("W8", (8,)), Point("W3", (3,)))),
    Fixture("initial_syscall.sv", "initial_syscall",
            (Port("x", 1),), (Port("y", 1),),
            expected_ordinary_refusal="Initial:runtime"),
    Fixture("initial_parameter_check.sv", "initial_parameter_check",
            (), (Port("y", 1),),
            (Point("N1", (1,)), Point("N0", (0,), ("ASRTST",)))),
    Fixture("multi_clock_domain.sv", "multi_clock_domain",
            (Port("aclk", 1, clock=True), Port("bclk", 1, clock=True), Port("d", 1)),
            (Port("x", 1), Port("y", 1))),
    Fixture("internal_clock_repro.sv", "internal_clock_repro",
            (Port("enable", 1), Port("data", 1)), (Port("result", 1),),
            expected_ordinary_refusal="Event:time-zero"),
    Fixture("function_call_expression_repro.sv", "function_call_expression_repro",
            (Port("in", 1),), (Port("y", 1),),
            expected_ordinary_refusal="CallExpression"),
    Fixture("interface_repro.sv", "interface_repro",
            (Port("clock", 1), Port("value", 1)), (Port("result", 1),),
            expected_ordinary_refusal="InstanceSymbol:interface",
            expected_source_refusals=("iverilog",)),
    Fixture("typed_variable_unpacked_scalar_repro.sv", "typed_variable_unpacked_scalar_repro",
            (Port("source", 4),), (Port("result", 4),),
            expected_source_refusals=("iverilog",)),
    Fixture("typed_variable_unpacked_repro.sv", "typed_variable_unpacked_repro",
            (Port("source", 4),), (Port("result", 4),),
            expected_ordinary_refusal="aggregate always_comb target path is invalid",
            expected_source_refusals=("iverilog",)),
    Fixture("typed_named_value_repro.sv", "typed_named_value_repro",
            (Port("i", 1),), (Port("result", 4),),
            expected_ordinary_refusal="MemberAccessExpression:aggregate: unknown index",
            expected_source_refusals=("iverilog",)),
    Fixture("member_nested_repro.sv", "member_nested_repro",
            (Port("i", 1),), (Port("result", 4),),
            expected_ordinary_refusal="MemberAccessExpression:aggregate: unknown index",
            expected_source_refusals=("iverilog",)),
    Fixture("type_alias_nested_repro.sv", "type_alias_nested_repro",
            (Port("source", 2),), (Port("result", 2),),
            expected_ordinary_refusal="TypeAliasType:TypeAlias",
            expected_source_refusals=("iverilog",)),
    Fixture("assignment_pattern_param_e.sv", "assignment_pattern_param_e",
            (Port("x", 4),), (Port("y", 4),),
            expected_loader_refusal="AssignmentPattern:default-point",
            expected_source_refusals=("iverilog",)),
    Fixture("assignment_pattern_packed_e.sv", "assignment_pattern_packed_e",
            (Port("x", 4),), (Port("y", 4),),
            expected_source_refusals=("iverilog",)),
    Fixture("assignment_pattern_positional_e.sv", "assignment_pattern_positional_e",
            (Port("x", 4),), (Port("y", 4),),
            expected_source_refusals=("iverilog",)),
    Fixture("assignment_pattern_replicated_e.sv", "assignment_pattern_replicated_e",
            (Port("x", 2),), (Port("y", 4),),
            expected_source_refusals=("iverilog", "xrun")),
    Fixture("latch_delay_e.sv", "latch_delay_e",
            (Port("en", 1), Port("a", 1)), (Port("q", 1),),
            expected_loader_refusal="TimingInFuncNotAllowed",
            expected_source_refusals=("iverilog", "xrun")),
    Fixture("latch_else_e.sv", "latch_else_e",
            (Port("en", 1), Port("d", 1)), (Port("q", 1),)),
    Fixture("latch_case_e.sv", "latch_case_e",
            (Port("sel", 2), Port("a", 4), Port("b", 4)), (Port("q", 4),)),
    Fixture("latch_function_e.sv", "latch_function_e",
            (Port("en", 1), Port("d", 1)), (Port("q", 1),),
            expected_ordinary_refusal="CallExpression:user-function"),
    Fixture("negedge_e.sv", "negedge_e",
            (Port("clk", 1, clock=True), Port("d", 1)), (Port("q", 1),)),
    Fixture("negedge_plain_e.sv", "negedge_plain_e",
            (Port("clk", 1, clock=True), Port("d", 1)), (Port("q", 1),)),
    Fixture("always_latch_e.sv", "always_latch_e",
            (Port("en", 1), Port("d", 1)), (Port("q", 1),)),
    Fixture("clk_arst.sv", "clk_arst",
            (Port("clk", 1, clock=True), Port("rst_n", 1, reset_active_low=True),
             Port("en", 1), Port("d", 4)), (Port("q", 4),),
            (Point("N4", (4,)),)),
    Fixture("clk_arst_comma.sv", "clk_arst_comma",
            (Port("clk", 1, clock=True), Port("rst_n", 1, reset_active_low=True),
             Port("en", 1), Port("d", 4)), (Port("q", 4),),
            (Point("N4", (4,)),)),
    Fixture("latch_array_e.sv", "latch_array_e",
            (Port("en", 1), Port("d", 4)), (Port("q", 4),)),
    Fixture("latch_generate_e.sv", "latch_generate_e",
            (Port("en", 2), Port("d", 4)), (Port("q", 4),),
            (Point("N2", (2,)), Point("N3", (3,)))),
    Fixture("latch_multi_e.sv", "latch_multi_e",
            (Port("en", 1), Port("a", 4), Port("b", 4)),
            (Port("q", 4), Port("r", 4))),
    Fixture("latch_cond_e.sv", "latch_cond_e",
            (Port("en", 1), Port("mode", 1), Port("d", 4)), (Port("q", 4),)),
    Fixture("latch_bit_e.sv", "latch_bit_e",
            (Port("en", 1), Port("idx", 2), Port("d", 1)), (Port("q", 4),),
            expected_ordinary_refusal="packed or concatenated always_comb target"),
    Fixture("latch_static_bit_e.sv", "latch_static_bit_e",
            (Port("en", 1), Port("d", 1)), (Port("q", 4),),
            expected_ordinary_refusal="packed or concatenated always_comb target"),
    Fixture("preempt_block_refuse.sv", "preemptive_schedule",
            (Port("a", 1), Port("b", 1)),
            (Port("q", 1), Port("r", 1), Port("z", 1))),
    Fixture("profile_mixed.sv", "profile_mixed",
            (Port("clk", 1, clock=True), Port("rst", 1, reset_active_low=True),
             Port("d", 1)), (Port("q", 1), Port("y", 1))),
    Fixture("signed_bit_select.sv", "signed_select",
            (Port("x", 8),), (Port("y", 1),)),
    Fixture("signed_decl.sv", "signed_comparison",
            (Port("x", 8),), (Port("y", 1),)),
    Fixture("timed_event_loop.sv", "timed_event_loop",
            (Port("x", 8),), (Port("y", 4),)),
    Fixture("implicit_clock_event.sv", "implicit_event",
            (Port("clk", 1, clock=True), Port("d", 1)), (Port("q", 1),),
            retain_proc_rewrites=True),
    Fixture("signal_event_control.sv", "signal_event_control",
            (Port("clk", 1, clock=True), Port("d", 1)), (Port("q", 1),),
            retain_proc_rewrites=True),
    Fixture("untyped_localparam_refuse.sv", "untyped_localparam_refuse",
            (Port("x", 1),), (Port("y", 1),)),
    Fixture("hierarchy_parameterized.sv", "hierarchy_parameterized",
            (Port("a", 8),), (Port("y", 8),),
            (Point("W8", (8,)),)),
    Fixture("inactive_generate_child_e.sv", "inactive_generate_child_e",
            (Port("a", 1),), (Port("y", 1),),
            (Point("USE0", (0,)), Point("USE1", (1,)))),
    Fixture("generate_unbound_parameter.sv", "generate_unbound_parameter_top",
            (Port("x", 1),), (Port("y", 1),),
            retain_proc_rewrites=True),
    Fixture("typed_unpacked_net.sv", "typed_unpacked_net",
            (Port("x", 8),), (Port("y", 8),)),
    Fixture("typed_port_repro.sv", "typed_port_repro",
            (Port("source", 5),), (Port("result", 4),)),
    Fixture("typed_port_pkg_repro.sv", "typed_port_pkg_repro",
            (Port("source", 5),), (Port("result", 4),)),
    Fixture("typed_port_enum_repro.sv", "typed_port_enum_repro",
            (Port("mode", 2),), (Port("result", 2),)),
    Fixture("bits_package_repro.sv", "bits_package_repro",
            (Port("x", 4),), (Port("y", 1),)),
    Fixture("bits_package_param_e.sv", "bits_package_param_e",
            (Port("x", 1),), (Port("y", 1),)),
    Fixture("bits_type_family_repro.sv", "bits_type_family_repro",
            (Port("x", 4),), (Port("y", 4),)),
    Fixture("bits_union_repro.sv", "bits_union_repro",
            (Port("x", 5),), (Port("y", 5),)),
    Fixture("bits_multidim_repro.sv", "bits_multidim_repro",
            (Port("x", 4),), (Port("y", 4),)),
    Fixture("bits_local_type_repro.sv", "bits_local_type_repro",
            (Port("x", 4),), (Port("y", 4),)),
    Fixture("typed_variable_repro.sv", "typed_variable_repro",
            (Port("d", 4),), (Port("q", 4),)),
    Fixture("typed_value_repro.sv", "typed_value_repro",
            (Port("source", 4),), (Port("result", 4),)),
    Fixture("type_alias_repro.sv", "type_alias_repro",
            (Port("source", 4),), (Port("result", 4),)),
    Fixture("output_net_z_generated_repro.sv", "output_net_z_generated_repro",
            (), (Port("y", 1),), retain_proc_rewrites=True),
    Fixture("initial_storage_repro.sv", "initial_storage_repro",
            (), (Port("q", 1),), retain_proc_rewrites=True),
    Fixture("child_instance_memory.sv", "child_instance_memory_parent",
            (Port("clk", 1, clock=True), Port("d", 1)), (Port("y", 1),),
            retain_proc_rewrites=True),
    Fixture("child_instance_scan.sv", "child_instance_scan",
            (Port("clk", 1, clock=True), Port("rst_n", 1, reset_active_low=True),
             Port("d", 1)), (Port("q", 1),), retain_proc_rewrites=True),
    Fixture("event_control_repro.sv", "event_control_repro",
            (Port("clk", 1, clock=True), Port("d", 1)), (Port("q", 1),),
            retain_proc_rewrites=True),
    Fixture("event_generated_repro.sv", "event_generated_repro",
            (Port("clk", 1, clock=True), Port("d", 1)), (Port("q", 1),),
            retain_proc_rewrites=True),
    Fixture("net_z_generated_repro.sv", "net_z_generated_repro",
            (Port("x", 1),), (Port("y", 1),), retain_proc_rewrites=True),
    Fixture("unsupported_instantiation_repro.sv", "unsupported_instantiation_repro",
            (Port("d", 1),), (Port("q", 1),), retain_proc_rewrites=True),
    Fixture("edge_child_instance.sv", "edge_parent",
            (Port("clk", 1, clock=True), Port("d", 1)), (Port("y", 1),),
            retain_proc_rewrites=True),
    Fixture("primitive_wire_repro.sv", "primitive_wire_repro",
            (Port("left", 1), Port("right", 1)), (Port("result", 1),)),
    Fixture("primitive_repro.sv", "primitive_repro",
            (Port("left", 1), Port("right", 1)), (Port("result", 1),),
            expected_source_refusals=("iverilog",)),
    Fixture("primitive_gate_family_e.sv", "primitive_gate_family_e",
            (Port("a", 1), Port("b", 1)),
            (Port("y_and", 1), Port("y_or", 1), Port("y_xor", 1), Port("y_xnor", 1))),
    Fixture("select_target_repro.sv", "select_target_repro",
            (Port("clk", 1, clock=True), Port("d", 1)), (Port("y", 1),),
            retain_proc_rewrites=True),
    Fixture("non_topological_assign.sv", "non_topological_assign",
            (Port("x", 1),), (Port("y", 1),), retain_proc_rewrites=True),
    Fixture("e_instantiation_repro.sv", "e_instantiation_repro_check",
            (Port("a", 1),), (Port("y", 1),), retain_proc_rewrites=True),
    Fixture("port_connection_target_repro.sv", "port_target_parent",
            (Port("d", 1),), (Port("y", 1),), retain_proc_rewrites=True),
    Fixture("port_connection_target_struct.sv", "struct_parent",
            (Port("d", 1),), (Port("y", 5),), retain_proc_rewrites=True),
    Fixture("unconditional_case2.sv", "unconditional_case2",
            (Port("source", 1),), (Port("result", 2),),
            retain_proc_rewrites=True),
    Fixture("hierarchical_value_repro.sv", "hierarchical_value_repro",
            (), (Port("result", 1),), retain_proc_rewrites=True),
    Fixture("member_access_repro.sv", "member_access_repro",
            (Port("source", 5),), (Port("result", 4),),
            retain_proc_rewrites=True),
    Fixture("member_index_repro.sv", "member_index_repro",
            (), (Port("result", 1),),
            retain_proc_rewrites=True),
    Fixture("member_range_repro.sv", "member_range_repro",
            (), (Port("result", 2),),
            retain_proc_rewrites=True),
    Fixture("packed_enum_integer_repro.sv", "packed_enum_integer_repro",
            (Port("x", 32),), (Port("y", 32),)),
    Fixture("packed_enum_package_repro.sv", "packed_enum_package_repro",
            (Port("mode", 1),), (Port("y", 1),)),
    Fixture("packed_enum_param_e.sv", "packed_enum_param_e",
            (Port("raw", 2),), (Port("y", 1),),
            (Point("W2", (2,)), Point("W4", (4,)))),
    Fixture("packed_enum_case_e.sv", "packed_enum_case_e",
            (Port("raw", 2),), (Port("y", 1),),
            (Point("W2", (2,)), Point("W4", (4,)))),
    Fixture("casez_casex_e.sv", "casez_casex_e",
            (Port("x", 4),), (Port("y", 2),)),
    Fixture("casex_e.sv", "casex_e",
            (Port("x", 4),), (Port("y", 2),)),
    Fixture("case_inside_e.sv", "case_inside_e",
            (Port("x", 4),), (Port("y", 2),),
            expected_loader_refusal="ValueRangeExpression",
            expected_source_refusals=("iverilog",)),
    Fixture("parameterized_storage_structure.sv", "parameterized_storage_structure",
            (Port("x", 8),), (Port("y", 8),),
            (Point("N1", (1,)), Point("N2", (2,)))),
    Fixture("net_z_signal.sv", "net_z_signal",
            (Port("x", 8),), (Port("y", 8),)),
    Fixture("assign_target.sv", "assign_target",
            (Port("x", 1),), (Port("y", 1),)),
    Fixture("typed_bit_localparam.sv", "typed_localparam",
            (Port("d", 1),), (Port("q", 1),)),
    Fixture("wire_output_port.sv", "wire_output_port",
            (Port("a", 8),), (Port("y", 8),)),
    Fixture("typed_array.sv", "typed_array",
            (Port("x", 8),), (Port("y", 8),),
            retain_proc_rewrites=True),
    Fixture("unbound_child_parameter.sv", "unbound_child_parameter_top",
            (Port("x", 8),), (Port("y", 8),),
            retain_proc_rewrites=True),
)


def run_checked(argv: list[str], cwd: Path, timeout: int = 120) -> str:
    proc = subprocess.Popen(argv, cwd=cwd, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            start_new_session=True)
    try:
        out, err = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        out, err = proc.communicate()
        raise RuntimeError(f"{' '.join(argv)} timed out:\n{out}{err}")
    if proc.returncode:
        raise RuntimeError(f"{' '.join(argv)} exited {proc.returncode}:\n{out}{err}")
    return out


def bits(value: int | str, width: int) -> str:
    if isinstance(value, str):
        return value * width
    return format(value & ((1 << width) - 1), f"0{width}b")


def port_width(fixture: Fixture, point: Point, port: Port) -> int:
    if fixture.top == "localparam_shift" and point.args:
        return point.args[0]
    if fixture.top == "memory_edge_loop" and point.args:
        return point.args[0]
    if fixture.top == "parameterized_size_cast_canonical_e" and point.args \
            and port.name == "y":
        return point.args[0]
    if fixture.top == "packed_shift_register_canonical_e" and point.args \
            and port.name == "q":
        return point.args[0]
    if fixture.top == "packed_enum_param_e" and point.args \
            and port.name == "raw":
        return point.args[0]
    if fixture.top == "packed_enum_dimension_repro" and point.args \
            and port.name == "raw":
        return point.args[0]
    if fixture.top == "packed_enum_case_e" and point.args \
            and port.name == "raw":
        return point.args[0]
    if fixture.top == "generated_array_nested" and point.args \
            and port.name in ("x", "taps"):
        return point.args[0]
    if fixture.top == "constant_function_top" and point.args:
        if port.name == "x":
            return point.args[0]
        if port.name == "y":
            return 1 if point.args[0] == 1 else 2
    if fixture.top == "generate_local_top" and point.args:
        return point.args[0]
    if fixture.top == "latch_generate_e" and point.args and port.name == "en":
        return point.args[0]
    return port.width


def stimuli(fixture: Fixture, point: Point, seed: int) -> list[dict[str, int | str]]:
    stable_tag = sum((i + 1) * ord(c) for i, c in enumerate(fixture.top + point.label))
    rng = random.Random(seed ^ stable_tag)
    result: list[dict[str, int | str]] = []
    for cycle in range(CYCLES):
        row: dict[str, int | str] = {}
        for port in fixture.inputs:
            if port.clock:
                # The x/z rows deliberately include clocks.  0/1 rows provide
                # ordinary edges before and after those unknown transitions.
                value: int | str = (0, 1, 0, 1, "x", "z", 0, 1)[cycle]
            elif cycle == 4:
                value = "x"
            elif cycle == 5:
                value = "z"
            elif port.reset_active_low and cycle == 0:
                value = 0
            elif port.reset_active_low:
                value = 1
            else:
                value = rng.randrange(1 << port_width(fixture, point, port))
            # The initial syscall is a safety check rather than a reset port.
            # Give its first sample a known one so the simulator's time-zero
            # initial block is independent of active-region ordering.
            if fixture.top == "initial_syscall" and port.name == "x" and cycle == 0:
                value = 1
            row[port.name] = value
        result.append(row)
    return result


def lean_literal(value: int | str, width: int) -> str:
    if isinstance(value, str):
        return f'LVec.lit "{value * width}"'
    return f"LVec.ofNat {width} {value}"


def lean_stimulus(rows: list[dict[str, int | str]], fixture: Fixture, point: Point) -> str:
    rendered = []
    for row in rows:
        fields = ", ".join(
            f'("{p.name}", {lean_literal(row[p.name], port_width(fixture, point, p))})'
            for p in fixture.inputs)
        rendered.append(f"[{fields}]")
    return "[" + ",\n   ".join(rendered) + "]"


def sv_literal(value: int | str, width: int) -> str:
    if isinstance(value, str):
        return f"{width}'b" + value * width
    return f"{width}'b" + format(value & ((1 << width) - 1), f"0{width}b")


def testbench(fixture: Fixture, point: Point, rows: list[dict[str, int | str]]) -> str:
    params = ""
    if point.args:
        names = {
            "constant_width_conversion": ("E",),
            "generate_parameter": ("W",),
            "localparam_shift": ("E",),
            "memory_edge_loop": ("W", "N"),
            "parameterized_unpacked_storage": ("N",),
            "parameterized_size_cast_canonical_e": ("W",),
            "packed_shift_register_canonical_e": ("N",),
            "generate_if_unpacked_array": ("N",),
            "generated_array_nested": ("W",),
            "hierarchy_parameterized": ("W",),
            "inactive_generate_child_e": ("USE",),
            "parameterized_storage_structure": ("N",),
            "initial_parameter_check": ("N",),
            "constant_function_top": ("N",),
            "generate_local_top": ("N",),
            "clk_arst": ("N",),
            "clk_arst_comma": ("N",),
            "latch_generate_e": ("N",),
            "proc_local_for_automatic": ("N",),
            "packed_enum_param_e": ("W",),
            "packed_enum_dimension_repro": ("W",),
            "packed_enum_case_e": ("W",),
        }[fixture.top]
        params = "#(" + ", ".join(f".{n}({v})" for n, v in zip(names, point.args)) + ")"
    declarations = []
    connections = []
    for p in fixture.inputs:
        width = port_width(fixture, point, p)
        typ = "logic" if width == 1 else f"logic [{width - 1}:0]"
        declarations.append(f"  {typ} {p.name};")
        connections.append(f".{p.name}({p.name})")
    for p in fixture.outputs:
        width = port_width(fixture, point, p)
        typ = "wire" if width == 1 else f"wire [{width - 1}:0]"
        declarations.append(f"  {typ} {p.name};")
        connections.append(f".{p.name}({p.name})")
    displays = " ".join(f"%b" for _ in fixture.outputs)
    display_args = ", ".join(p.name for p in fixture.outputs)
    assignments = []
    for i, row in enumerate(rows):
        assignments.extend(f"    {p.name} = {sv_literal(row[p.name], port_width(fixture, point, p))};"
                           for p in fixture.inputs)
        assignments.append(f"    #1 $display(\"ROW {i} {displays}\", {display_args});")
    return "\n".join([
        "`timescale 1ns/1ps",
        f"module batch_tb;",
        *declarations,
        f"  {fixture.top} {params} dut ({', '.join(connections)});",
        "  initial begin",
        *assignments,
        "    $finish;",
        "  end",
        "endmodule",
        "",
    ])


def lean_program(entries: list[tuple[Fixture, Point, Path, list[dict[str, int | str]]]]) -> str:
    loads = []
    runs = []
    for number, (fixture, point, envelope, rows) in enumerate(entries):
        name = f"batch_{number}_{re.sub('[^A-Za-z0-9]', '_', fixture.top)}"
        loads.append(f'load_design_sv2 {name} from "{envelope}"')
        args = " ".join(str(x) for x in point.args)
        family = f"{name}.e" + ((" " + args) if args else "")
        stim = lean_stimulus(rows, fixture, point)
        outs = "[" + ", ".join(f'"{p.name}"' for p in fixture.outputs) + "]"
        runs.append(f'#eval emit "{fixture.top}" "{point.label}" ({family}) {stim} {outs}')
    return "\n".join([
        "import LeanModels.Sv.Ingest2",
        "import LeanModels.Sv.Kernel.CoreMemExec",
        "open LeanModels.Sv",
        "open LeanModels.Sv.Kernel",
        "set_option maxRecDepth 100000",
        "",
        *loads,
        "",
        "def runRows (d : CoreMemDesign) (s : CoreMemState) : List SvState → Res (List CoreMemState)",
        "  | [] => .ok []",
        "  | row :: rest => do",
        "      let s' ← d.step s row",
        "      let tail ← runRows d s' rest",
        "      .ok (s' :: tail)",
        "",
        "def emitRows (tag point : String) (d : CoreMemDesign) (rows : List CoreMemState)",
        "    (names : List String) (i : Nat) : IO Unit :=",
        "  match rows with",
        "  | [] => pure ()",
        "  | s :: rest => do",
        "      let vals := names.map (SvState.showSignal (CoreMemState.view d s))",
        "      IO.println (\"E \" ++ tag ++ \" \" ++ point ++ \" \" ++ toString i ++ \" \" ++ String.intercalate \" \" vals)",
        "      emitRows tag point d rest names (i + 1)",
        "",
        "def emit (tag point : String) (r : Res CoreMemDesign) (stim : List SvState)",
        "    (names : List String) : IO Unit :=",
        "  match r with",
        "  | .ok d =>",
        "      match d.initialState with",
        "      | .ok s =>",
        "          match runRows d s stim with",
        "          | .ok rows => emitRows tag point d rows names 0",
        "          | .timeout => IO.println (\"ERROR \" ++ tag ++ \" \" ++ point ++ \" timeout\")",
        "          | .unsupported e => IO.println (\"ERROR \" ++ tag ++ \" \" ++ point ++ \" \" ++ e)",
        "      | .timeout => IO.println (\"ERROR \" ++ tag ++ \" \" ++ point ++ \" initial-timeout\")",
        "      | .unsupported e => IO.println (\"ERROR \" ++ tag ++ \" \" ++ point ++ \" \" ++ e)",
        "  | .timeout => IO.println (\"ERROR \" ++ tag ++ \" \" ++ point ++ \" instantiate-timeout\")",
        "  | .unsupported e => IO.println (\"ERROR \" ++ tag ++ \" \" ++ point ++ \" \" ++ e)",
        "",
        *runs,
        "def main : IO Unit := pure ()",
        "",
    ])


def parse_rows(text: str, prefix: str) -> dict[tuple[str, str], list[list[str]]]:
    result: dict[tuple[str, str], list[list[str]]] = {}
    for line in text.splitlines():
        parts = line.split()
        if len(parts) < 5 or parts[0] != prefix:
            continue
        key = (parts[1], parts[2])
        result.setdefault(key, []).append(parts[4:])
    return result


def simulator_rows(text: str, fixture: Fixture) -> list[list[str]]:
    result = []
    for line in text.splitlines():
        parts = line.split()
        if len(parts) >= 2 + len(fixture.outputs) and parts[0] == "ROW":
            result.append(parts[2:])
    return result


def run_simulator(sim: str, fixture: Fixture, point: Point,
                  rows: list[dict[str, int | str]], source: Path, work: Path) -> tuple[str, list[list[str]]]:
    tb = work / "batch_tb.sv"
    tb.write_text(testbench(fixture, point, rows))
    sources = [str(source), str(tb)]
    if sim == "iverilog":
        exe = work / "sim.out"
        run_checked(["iverilog", "-g2012", "-s", "batch_tb", "-o", str(exe)] + sources,
                    work)
        out = run_checked(["vvp", str(exe)], work)
    else:
        try:
            out = run_checked(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                               "-top", "batch_tb"] + sources, work)
        except RuntimeError as exc:
            # Xcelium returns status 1 for an assertion `$error` even after
            # the testbench reaches `$finish`.  This is an expected source
            # diagnostic only for points that declare its exact marker; all
            # other simulator failures remain hard receipt failures.
            detail = str(exc)
            if (point.expected_simulator_diagnostics and
                    all(marker in detail for marker in point.expected_simulator_diagnostics) and
                    "Simulation complete via $finish" in detail):
                out = detail
            else:
                raise
    return out, simulator_rows(out, fixture)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cleanroom-dir", type=Path, default=Path("cleanroom"),
                        help="directory containing the census .sv fixtures")
    parser.add_argument("--seed", type=lambda x: int(x, 0), default=SEED)
    parser.add_argument("--lean-group-size", type=int, default=2,
                        help="number of fixture points per ordinary Lean process")
    parser.add_argument("--ordinary-timeout", type=int, default=120,
                        help="seconds allowed for one ordinary Lean group")
    parser.add_argument("--only", nargs="*", default=None,
                        help="optional fixture tops to measure (default: all)")
    args = parser.parse_args()
    cleanroom = args.cleanroom_dir.resolve()
    if not cleanroom.is_dir():
        raise SystemExit(f"clean-room directory does not exist: {cleanroom}")
    if not shutil.which("iverilog") or not shutil.which("vvp"):
        raise SystemExit("Icarus Verilog 13.0 is required")
    simulators = ["iverilog"]
    if shutil.which("xrun"):
        simulators.append("xrun")
    print(f"seed=0x{args.seed:x} cycles={CYCLES}")
    iverilog_version = run_checked(["iverilog", "-V"], ROOT, timeout=30).splitlines()[0]
    print("Icarus:", iverilog_version)
    xrun_version = "unavailable"
    if "xrun" in simulators:
        xrun_version = run_checked(["xrun", "-version"], ROOT, timeout=30).splitlines()[0]
        print("Xcelium:", xrun_version)

    with tempfile.TemporaryDirectory(prefix="sv-batch-") as tmp_name:
        tmp = Path(tmp_name)
        entries = []
        ordinary_entries = []
        fixtures = tuple(f for f in FIXTURES if args.only is None or f.top in args.only)
        if not fixtures:
            raise SystemExit("--only selected no known fixture")
        for fixture in fixtures:
            source = cleanroom / fixture.source
            if not source.exists():
                raise SystemExit(f"missing fixture: {source}")
            flags = ["--top", fixture.top]
            if fixture.retain_proc_rewrites:
                flags.append("--retain-proc-rewrites")
            if fixture.retain_loops:
                flags.append("--retain-loops")
            envelope = tmp / f"{fixture.top}.sv.json"
            run_checked([sys.executable, str(EXTRACT), *flags, "-o", str(envelope), str(source)], ROOT)
            for point in fixture.points:
                rows = stimuli(fixture, point, args.seed)
                entries.append((fixture, point, envelope, rows))
                if not fixture.expected_loader_refusal:
                    ordinary_entries.append((fixture, point, envelope, rows))

        # Keeping a few source-shaped designs per generated Lean file avoids a
        # single enormous kernel reduction while preserving one top-level batch
        # command and one shared manifest.  The resulting ordinary rows are
        # still collected before either simulator is run.
        ordinary: dict[tuple[str, str], list[list[str]]] = {}
        ordinary_errors: dict[tuple[str, str], str] = {}
        errors: list[str] = []
        group_size = max(1, args.lean_group_size)
        for group_no in range(0, len(ordinary_entries), group_size):
            group = ordinary_entries[group_no:group_no + group_size]
            lean_file = tmp / f"batch_{group_no // group_size}.lean"
            lean_file.write_text(lean_program(group))
            print(f"ordinary group {group_no // group_size + 1}/{(len(ordinary_entries) + group_size - 1) // group_size}",
                  flush=True)
            try:
                lean_out = run_checked(["lake", "env", "lean", "--run", str(lean_file)], ROOT,
                                       timeout=args.ordinary_timeout)
            except RuntimeError as exc:
                errors.append(f"ERROR ordinary group {group_no // group_size + 1}: {exc}")
                continue
            for key, rows in parse_rows(lean_out, "E").items():
                ordinary[key] = rows
            for line in lean_out.splitlines():
                if not line.startswith("ERROR "):
                    continue
                errors.append(line)
                parts = line.split(" ", 3)
                if len(parts) == 4 and parts[1] != "ordinary":
                    ordinary_errors[(parts[1], parts[2])] = parts[3]
        for fixture, point, envelope, _rows in entries:
            if not fixture.expected_loader_refusal:
                continue
            key = (fixture.top, point.label)
            census = run_checked(["lake", "env", "lean", "--run",
                                  str(ROOT / "harness" / "sv" / "refusal_census.lean"),
                                  str(envelope)], ROOT, timeout=args.ordinary_timeout)
            if fixture.expected_loader_refusal in census:
                ordinary_errors[key] = fixture.expected_loader_refusal
            else:
                errors.append(f"ERROR {fixture.top} {point.label} loader refusal marker missing")
        if errors:
            print("ordinary-route errors:")
            print("\n".join(errors))

        all_match = True
        for fixture, point, envelope, rows in entries:
            key = (fixture.top, point.label)
            expected = ordinary.get(key, [])
            print(f"FIXTURE {fixture.top} {point.label}: ordinary={len(expected)} "
                  f"Icarus={iverilog_version} Xcelium={xrun_version}")
            if len(expected) != CYCLES:
                ordinary_error = ordinary_errors.get(key, "")
                expected_e_refusal = (fixture.expected_ordinary_refusal != "" and
                                      fixture.expected_ordinary_refusal in ordinary_error)
                expected_e_refusal = expected_e_refusal or (
                    fixture.expected_loader_refusal != "" and
                    fixture.expected_loader_refusal in ordinary_error)
                if expected_e_refusal:
                    print(f"  RUNS NO (expected ordinary refusal: {ordinary_error})")
                else:
                    print(f"  RUNS NO (ordinary route returned {len(expected)} cycles)")
                expected_refusals = set(fixture.expected_source_refusals)
                if not expected_e_refusal:
                    all_match = False
                # Still run both pinned source simulators.  There is no E
                # comparison for this point, but the source rows make the
                # refusal/timeout measurable rather than silently skipped.
                source_rows: dict[str, list[list[str]]] = {}
                source_refusals: set[str] = set()
                for sim in simulators:
                    source = cleanroom / fixture.source
                    with tempfile.TemporaryDirectory(prefix="sv-batch-sim-") as sim_name:
                        try:
                            _, actual = run_simulator(sim, fixture, point, rows, source, Path(sim_name))
                        except RuntimeError as exc:
                            if sim in expected_refusals:
                                source_refusals.add(sim)
                                print(f"  {sim}: EXPECTED SOURCE REFUSAL {exc}")
                            else:
                                print(f"  {sim}: ERROR {exc}")
                                all_match = False
                            continue
                    source_rows[sim] = actual
                    print(f"  {sim}: {len(actual)} source cycles (no E comparison)")
                    for i, row in enumerate(actual):
                        print(f"  SOURCE CYCLE {i} {sim} {' '.join(row)}")
                if source_refusals != expected_refusals:
                    print(f"  SOURCE REFUSAL SET DIVERGE expected={sorted(expected_refusals)} "
                          f"actual={sorted(source_refusals)}")
                    all_match = False
                if len(source_rows) == 2:
                    left, right = (source_rows[s] for s in simulators)
                    for i, (lrow, rrow) in enumerate(zip(left, right)):
                        verdict = "MATCH" if lrow == rrow else "DIVERGE"
                        print(f"  SOURCE CYCLE {i} {verdict} {simulators[0]}={' '.join(lrow)} "
                              f"{simulators[1]}={' '.join(rrow)}")
                        if verdict == "DIVERGE":
                            all_match = False
                continue
            for sim in simulators:
                source = cleanroom / fixture.source
                with tempfile.TemporaryDirectory(prefix="sv-batch-sim-") as sim_name:
                    try:
                        sim_out, actual = run_simulator(sim, fixture, point, rows, source, Path(sim_name))
                    except RuntimeError as exc:
                        if sim in fixture.expected_source_refusals:
                            print(f"  {sim}: EXPECTED SOURCE REFUSAL {exc}")
                            continue
                        print(f"  {sim}: ERROR {exc}")
                        all_match = False
                        continue
                print(f"  {sim}: {len(actual)} source cycles")
                if (point.expected_simulator_diagnostics and
                        all(marker in sim_out for marker in point.expected_simulator_diagnostics)):
                    print(f"  {sim}: accepted expected diagnostic "
                          f"{', '.join(point.expected_simulator_diagnostics)}")
                for i, (e_row, s_row) in enumerate(zip(expected, actual)):
                    verdict = "MATCH" if e_row == s_row else "DIVERGE"
                    print(f"  CYCLE {i} {sim} {verdict} E={' '.join(e_row)} S={' '.join(s_row)}")
                    if verdict == "DIVERGE":
                        all_match = False
                if len(actual) != CYCLES:
                    print(f"  CYCLE COUNT {sim} DIVERGE expected={CYCLES} actual={len(actual)}")
                    all_match = False
        return 0 if all_match else 1


if __name__ == "__main__":
    raise SystemExit(main())
