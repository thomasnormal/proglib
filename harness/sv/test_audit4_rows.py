"""Pinned Audit 4 differential rows and oracle provenance."""
import json
import unittest
from pathlib import Path


ROWS = Path(__file__).with_name("audit4_rows.json")


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
