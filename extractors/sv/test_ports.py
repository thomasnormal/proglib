"""Port-shape admission for the legacy/self-check envelope."""

import json
import os
import tempfile
import unittest

import extract
from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree


def lower(source):
    extract._SYM = None
    extract._SOURCE_BYTES = source.encode()
    tree = SyntaxTree.fromText(source)
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    return extract.convert_design(tree.sourceManager, compilation)


def nodes(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from nodes(child)


class Ports(unittest.TestCase):
    def test_signed_four_state_ports_are_admitted_with_metadata(self):
        design = lower(
            'module e(input logic signed [7:0] a, output logic signed [7:0] b); '
            'assign b = a; endmodule'
        )
        ports = design["modules"][0]["ports"]
        self.assertEqual([port.get("signed", False) for port in ports], [True, True])
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_signed_relational_operator_keeps_signed_tag(self):
        design = lower(
            'module e(input logic signed [7:0] a, b, output logic lt); '
            'assign lt = a < b; endmodule'
        )
        binary = next(node for node in nodes(design) if node.get("kind") == "Binary")
        self.assertEqual(binary["op"], "s<")
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_two_state_output_port_is_admitted(self):
        design = lower(
            'module e(output bit a); initial begin if (a == 1\'b0) $finish; end endmodule'
        )
        port = design["modules"][0]["ports"][0]
        self.assertEqual(port["width"], 1)
        self.assertTrue(port["two_state"])

    def test_signed_two_state_output_port_is_admitted(self):
        design = lower(
            'module e(output bit signed [3:0] a); '
            'initial begin if (a == 4\'b0000) $finish; end endmodule'
        )
        port = design["modules"][0]["ports"][0]
        self.assertEqual(port["width"], 4)
        self.assertTrue(port["two_state"])
        self.assertTrue(port["signed"])

    def test_two_state_input_port_is_admitted(self):
        design = lower(
            'module e(input bit a); initial begin if (a == 1\'b0) $finish; end endmodule'
        )
        port = design["modules"][0]["ports"][0]
        self.assertTrue(port["two_state"])
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_signed_two_state_input_port_is_admitted(self):
        design = lower(
            'module e(input bit signed [3:0] a); initial $finish; endmodule'
        )
        port = design["modules"][0]["ports"][0]
        self.assertTrue(port["two_state"])
        self.assertTrue(port["signed"])
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_predefined_integral_variable_ports(self):
        for spelling, width, signed, two_state in [
            ("byte", 8, True, True), ("shortint", 16, True, True),
            ("int", 32, True, True), ("longint", 64, True, True),
            ("integer", 32, True, False), ("time", 64, False, False),
        ]:
            for direction in ("input", "output"):
                with self.subTest(spelling=spelling, direction=direction):
                    design = lower(f"module e({direction} {spelling} value); endmodule")
                    port = design["modules"][0]["ports"][0]
                    self.assertEqual(port["width"], width)
                    self.assertEqual(port.get("signed", False), signed)
                    self.assertEqual(port.get("two_state", False), two_state)
                    self.assertFalse(any(node.get("kind") == "Unsupported"
                                         for node in nodes(design)))

    def test_two_state_net_input_remains_loud(self):
        design = lower("module e(input wire bit a); endmodule")
        self.assertTrue(any(node.get("sv_kind") == "PortSymbol:2state"
                            for node in nodes(design)))

    def test_port_initializers_are_not_dropped(self):
        for declaration in ("input bit value = 1", "output bit value = 1",
                            "input int value = 7", "output integer value = 7"):
            with self.subTest(declaration=declaration):
                design = lower(f"module sample({declaration}); endmodule")
                port = design["modules"][0]["ports"][0]
                self.assertIn("init", port)
                self.assertFalse(any(node.get("kind") == "Unsupported"
                                     for node in nodes(design)))

    def test_output_net_initializer_remains_loud(self):
        design = lower("module sample(output wire value = 1'b1); endmodule")
        self.assertTrue(any(node.get("sv_kind") == "PortSymbol:net-initializer"
                            for node in nodes(design)))

    def test_non_ansi_variable_port_initializer_is_retained(self):
        design = lower("module sample(value); output value; bit value = 1; endmodule")
        port = design["modules"][0]["ports"][0]
        self.assertTrue(port["two_state"])
        self.assertIn("init", port)
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_two_state_net_output_remains_loud(self):
        design = lower(
            'module e(output wire bit a); initial begin $finish; end endmodule'
        )
        self.assertTrue(any(
            node.get("sv_kind") == "PortSymbol:2state" for node in nodes(design)
        ))

    def test_comma_separated_ansi_ports_retain_inherited_packed_width(self):
        # IEEE 1800-2023 §23.2.2.3: a later identifier in an ANSI port list
        # inherits the direction, port kind, data type and packed dimensions
        # of the port before it.
        design = lower(
            'module e #(parameter int W = 4) '
            '(input wire [W-1:0] a, b, output logic [W-1:0] c, d); '
            'assign c = a; assign d = b; endmodule'
        )
        self.assertEqual([port["width"] for port in design["modules"][0]["ports"]],
                         [4, 4, 4, 4])
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_comma_separated_ansi_ports_inherit_symbolic_packed_dimensions(self):
        # The same rule in the symbolic (`--top`) envelope: every identifier of
        # a net list and of a variable list carries the first identifier's
        # parameter-dependent packed dimension.  A `packed: null` here is what
        # the Lean loader refuses as "unrecoverable packed dimensions".
        source = ('module e #(parameter integer P = 3, parameter integer Q = 4) '
                  '(input wire clk, input wire [P+Q:0] a, b, '
                  'output logic [P+Q:0] x, y); '
                  'assign x = a ^ b; always_ff @(posedge clk) y <= a + b; endmodule\n')
        with tempfile.TemporaryDirectory() as directory:
            src = os.path.join(directory, "e.sv")
            out = os.path.join(directory, "e.sv.json")
            with open(src, "w") as handle:
                handle.write(source)
            extract.process_symbolic("e", [src], [], out)
            with open(out) as handle:
                module = json.load(handle)["design"]["modules"][0]
        ports = {port["name"]: port["width"] for port in module["ports"]}

        def shape(node):
            if isinstance(node, dict):
                return {k: shape(v) for k, v in node.items() if k != "span"}
            if isinstance(node, list):
                return [shape(v) for v in node]
            return node

        for first, later in (("a", "b"), ("x", "y")):
            self.assertIsNotNone(ports[later]["packed"])
            self.assertEqual(shape(ports[first]), shape(ports[later]))
            self.assertEqual(ports[later]["resolved"], 8)
