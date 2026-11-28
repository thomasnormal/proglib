import json
import unittest
from pathlib import Path

ROWS = Path(__file__).with_name("audit6_rows.json")


class Audit6Rows(unittest.TestCase):
    def test_int_min_rows_pin_value_and_nontermination(self):
        data = json.loads(ROWS.read_text())
        rows = {row["name"]: row for row in data["rows"]}
        near = rows["audit6_near_min"]
        self.assertEqual(near["kind"], "answer")
        self.assertEqual(near["iverilog"], "00000007,00000007,00000007")
        self.assertEqual(near["iverilog"], near["xcelium"])
        infinite = rows["audit6_inf_ge_min"]
        self.assertEqual(infinite["kind"], "refusal")
        self.assertEqual(infinite["refusal"], "ForLoopStatement")
        nested = rows["audit6_nest_same_ext"]
        self.assertEqual(nested["kind"], "refusal")
        self.assertEqual(nested["refusal"], "ForLoopStatement")


if __name__ == "__main__":
    unittest.main()
