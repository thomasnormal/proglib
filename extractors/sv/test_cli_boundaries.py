"""CLI boundaries for the approved Slang extractor frontend."""

from pathlib import Path
import json
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
EXTRACT = ROOT / "extractors/sv/extract.py"


class CliBoundaries(unittest.TestCase):
    def test_retain_proc_rewrites_is_recorded_in_symbolic_envelope(self):
        with tempfile.TemporaryDirectory(prefix="sv-cli-proc-mode-") as td:
            source = Path(td) / "top.sv"
            source.write_text(
                "module top(input logic a, output logic y);\n"
                "  always @* y = a;\n"
                "endmodule\n")
            for retained in (False, True):
                output = Path(td) / ("retained.json" if retained else "lowered.json")
                flags = ["--top", "top", "-o", str(output)]
                if retained:
                    flags.append("--retain-proc-rewrites")
                proc = subprocess.run(
                    [sys.executable, str(EXTRACT), *flags, str(source)],
                    cwd=ROOT, text=True, capture_output=True)
                self.assertEqual(proc.returncode, 0, proc.stderr)
                envelope = json.loads(output.read_text())
                self.assertEqual(envelope.get("retain_proc_rewrites", False), retained)

    def test_retain_loops_requires_symbolic_top(self):
        with tempfile.TemporaryDirectory(prefix="sv-cli-loop-") as td:
            source = Path(td) / "top.sv"
            source.write_text("module top; initial begin int i; for (i=0;i<1;i++) ; end endmodule\n")
            proc = subprocess.run(
                [sys.executable, str(EXTRACT), "--retain-loops", str(source)],
                cwd=ROOT, text=True, capture_output=True)
            self.assertNotEqual(proc.returncode, 0)
            self.assertIn("--retain-loops requires --top", proc.stderr)

    def test_define_is_accepted_in_flat_mode(self):
        with tempfile.TemporaryDirectory(prefix="sv-cli-define-") as td:
            source = Path(td) / "top.sv"
            source.write_text("`ifdef FLAG\nmodule top; endmodule\n`endif\n")
            proc = subprocess.run(
                [sys.executable, str(EXTRACT), "-D", "FLAG", str(source)],
                cwd=ROOT, text=True, capture_output=True)
            self.assertEqual(proc.returncode, 0, proc.stderr)


if __name__ == "__main__":
    unittest.main()
