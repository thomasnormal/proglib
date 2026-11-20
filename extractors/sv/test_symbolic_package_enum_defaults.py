"""Package enum metadata in sv-0.2 parameter defaults."""

import json
import tempfile
import unittest
from pathlib import Path

import extract


class SymbolicPackageEnumDefaults(unittest.TestCase):
    def test_scalar_package_enum_keeps_empty_packed_shape(self):
        source = (
            "package p; typedef enum logic {IDLE=1'b0, RUN=1'b1} state_t; "
            "endpackage module top(input p::state_t state, output logic y); "
            "always_comb y = (state == p::IDLE); endmodule"
        )
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "top.sv"
            out = Path(directory) / "top.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            module = json.loads(out.read_text())["design"]["modules"][0]

        enum = module["types"][0]
        self.assertEqual(enum["name"], "state_t")
        self.assertEqual(enum["base_width"], {
            "kind": "PackedType", "packed": [], "resolved": 1})

    def test_integer_enum_keeps_fixed_predefined_width(self):
        source = (
            "package p; typedef enum integer {IDLE=0, RUN=1} state_t; "
            "endpackage module top #(parameter p::state_t S = p::IDLE) "
            "(output logic y); always_comb y = (S == p::IDLE); endmodule"
        )
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "top.sv"
            out = Path(directory) / "top.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            module = json.loads(out.read_text())["design"]["modules"][0]

        enum = module["types"][0]
        self.assertEqual(enum["base_width"], {
            "kind": "PackedType",
            "packed": [{
                "msb": {"kind": "Int", "span": None,
                        "value": 31, "resolved_width": None},
                "lsb": {"kind": "Int", "span": None,
                        "value": 0, "resolved_width": None},
            }],
            "resolved": 32,
        })

    def test_qualified_enum_default_stays_source_shaped(self):
        source = (
            "package p; typedef enum logic [1:0] {IDLE=0, RUN=1} state_t; "
            "endpackage module top #(parameter p::state_t S = p::RUN) ("
            "input logic [1:0] a, output logic [1:0] y); "
            "always_comb if (a == S) y = p::RUN; else y = p::IDLE; endmodule"
        )
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "top.sv"
            out = Path(directory) / "top.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            module = json.loads(out.read_text())["design"]["modules"][0]

        param = module["params"][0]
        self.assertEqual(param["type"]["kind"], "TypeRef")
        self.assertEqual(param["type"]["from_package"], "p")
        self.assertEqual(param["default"]["kind"], "EnumRef")
        self.assertEqual(param["default"]["from_package"], "p")
        self.assertEqual(param["default"]["member"], "RUN")
        self.assertEqual([(t["name"], t["from_package"])
                          for t in module["types"]], [("state_t", "p")])
        self.assertFalse(any(n.get("kind") == "Unsupported"
                             for n in module["processes"]))

    def test_package_enum_alias_recovers_fixed_packed_shape(self):
        source = (
            "package p; typedef logic [3:0] mask_t; "
            "typedef enum mask_t {CLR=4'h1, SET=4'h2} action_t; "
            "endpackage module top(input p::action_t action, output logic y); "
            "always_comb y = (action == p::CLR); endmodule"
        )
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "top.sv"
            out = Path(directory) / "top.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            module = json.loads(out.read_text())["design"]["modules"][0]

        enum = next(t for t in module["types"] if t["name"] == "action_t")
        self.assertEqual(enum["base_width"]["packed"][0]["msb"]["value"], 3)
        self.assertEqual(enum["base_width"]["packed"][0]["lsb"]["value"], 0)
        self.assertEqual(enum["base_width"]["resolved"], 4)


if __name__ == "__main__":
    unittest.main()
