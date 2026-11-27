"""Pinned Audit 4 differential rows and oracle provenance."""
import json
import subprocess
import sys
import unittest
from pathlib import Path


ROWS = Path(__file__).with_name("audit4_rows.json")
CASES = Path(__file__).with_name("cases2.json")
REPO = Path(__file__).resolve().parents[2]


class Audit4Rows(unittest.TestCase):
    def test_rows_have_pinned_oracles_and_outcomes(self):
        data = json.loads(ROWS.read_text())
        self.assertEqual(data["simulators"]["xcelium"], "Xcelium 26.09 via fleet reference runner")
        rows = data["rows"]
        self.assertEqual(len({row["name"] for row in rows}), len(rows))
        for row in rows:
            self.assertIn(row["kind"], ("answer", "refusal"))
            if row["kind"] == "answer":
                self.assertEqual(row["iverilog"], row["xcelium"])
            else:
                self.assertTrue(row["model"])

    def test_audit_rows_run_on_canonical_e(self):
        """Exercise every Audit 4 row through the changed canonical-E path.

        The ordinary sv2 harness defaults to the retiring run2 backend.  This
        explicit step keeps the loop-fuel regressions on the executor that the
        branch changes, and a zero-row collection is a failure.
        """
        cases = json.loads(CASES.read_text())["cases"]
        names = ["audit4_dep3i", "audit4_dep10i", "audit4_nest_dep_p1k",
                 "audit4_q_init_mem", "a5_long_answer"]
        available = {case["name"] for case in cases}
        self.assertTrue(set(names) <= available)
        command = [sys.executable, str(REPO / "harness/sv/diff_test2.py"),
                   "--backend", "ecanon", "--sim", "iverilog", "--no-xcheck"]
        for name in names:
            command.extend(("--case", name))
        result = subprocess.run(command, cwd=REPO, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        completed = sum(any(line.startswith(name + " ") for line in result.stdout.splitlines())
                        for name in names)
        self.assertEqual(completed, len(names), result.stdout)
        self.assertEqual(result.returncode, 0, result.stdout)


if __name__ == "__main__":
    unittest.main()
