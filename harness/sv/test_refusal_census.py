"""Receipt checks for the collect-all extractor/ordinary refusal census."""
import json
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
RECEIPT = ROOT / "Examples/system-verilog/sem2/refusal_census_three_walls/census.jsonl"



class RefusalCensus(unittest.TestCase):
    def test_three_independent_walls_have_both_receipts(self):
        rows = [json.loads(line) for line in RECEIPT.read_text().splitlines()]
        self.assertEqual(len(rows), 10)
        self.assertEqual({row["stage"] for row in rows}, {"extractor", "ordinary"})
        for stage in ("extractor", "ordinary"):
            selected = [row for row in rows if row["stage"] == stage]
            self.assertEqual(len(selected), 5)
            self.assertTrue(all(isinstance(row["line"], int) for row in selected))
            self.assertGreaterEqual(len({row["construct"] for row in selected}), 3)
            self.assertTrue(all(row["function"] for row in selected))
