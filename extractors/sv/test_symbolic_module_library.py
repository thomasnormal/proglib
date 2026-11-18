"""Source-shaped module libraries retain definitions behind inactive generates."""

import json
import tempfile
import unittest
from pathlib import Path

import extract


class SymbolicModuleLibrary(unittest.TestCase):
    def test_inactive_generate_child_definition_is_retained(self):
        source = """
module child(input logic a, output logic y);
  assign y = a;
endmodule
module top #(parameter bit USE = 0)
    (input logic a, output logic y);
  if (USE) begin : g
    child u(.a(a), .y(y));
  end else begin
    assign y = 1'b0;
  end
endmodule
"""
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "fixture.sv"
            out = Path(directory) / "fixture.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            names = [m["name"] for m in json.loads(out.read_text())["design"]["modules"]]
        self.assertEqual(names, ["top", "child"])


if __name__ == "__main__":
    unittest.main()
