#!/usr/bin/env python3
"""Print the reproducible scalar tables for a rust-stage0 measurement JSON."""
from __future__ import annotations
import argparse
import json
import statistics
from collections import Counter
from pathlib import Path


def totals(row, section, partition=None):
    if partition is None:
        return tuple(sum(value[section] for value in row["static"]["reachable"].values()) for section in ("bodies", "blocks", "statements"))
    return tuple(row["executed"]["by_partition"][partition][section] for section in ("bodies", "blocks", "statements"))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("report", type=Path)
    args = parser.parse_args()
    data = json.loads(args.report.read_text(encoding="utf-8"))
    rows = data["rows"]
    print("id,category,reachable_bodies,reachable_blocks,reachable_statements,executed_bodies,executed_blocks,executed_statements,user_exec_bodies,user_exec_blocks,user_exec_statements,std_exec_bodies,std_exec_blocks,std_exec_statements")
    for row in rows:
        rb, rbl, rs = totals(row, "bodies")
        ex = row["executed"]["executed"]
        user = totals(row, "bodies", "user")
        std = totals(row, "bodies", "std")
        print(",".join(map(str, [row["id"], row["category"], rb, rbl, rs,
                                  ex["bodies"], ex["blocks"], ex["statements"],
                                  *user, *std])))
    print("\ncategory,count,reachable_bodies_median,reachable_blocks_median,reachable_statements_median,executed_bodies_median,executed_blocks_median,executed_statements_median")
    for category in sorted({row["category"] for row in rows}):
        group = [row for row in rows if row["category"] == category]
        reach = [totals(row, "bodies") for row in group]
        execute = [tuple(row["executed"]["executed"][section] for section in ("bodies", "blocks", "statements")) for row in group]
        print(",".join(map(str, [category, len(group), *[statistics.median(x[index] for x in reach) for index in range(3)], *[statistics.median(x[index] for x in execute) for index in range(3)]])))
    print("\nexecuted_node_kind,count")
    nodes = Counter()
    for row in rows:
        nodes.update(row["executed"]["node_counts"])
    for key, value in sorted(nodes.items()):
        print(f"{key},{value}")
    print("\nconstruct,parameter,user_bodies,user_blocks,user_statements")
    for row in data.get("construct_sizes", []):
        print(",".join(str(row[key]) for key in ("construct", "parameter", "user_bodies", "user_blocks", "user_statements")))
    print("\nreachable_partition_totals,partition,bodies,blocks,statements")
    for partition in ("user", "std", "other"):
        print(",".join(map(str, ["reachable_partition_totals", partition, *[sum(row["static"]["reachable"][partition][section] for row in rows) for section in ("bodies", "blocks", "statements")]])))
    print("executed_partition_totals,partition,bodies,blocks,statements")
    for partition in ("user", "std", "other"):
        print(",".join(map(str, ["executed_partition_totals", partition, *[sum(row["executed"]["by_partition"][partition][section] for row in rows) for section in ("bodies", "blocks", "statements")]])))
    print("\nintrinsics")
    for name in sorted({name for row in rows for name in row["intrinsics_reached"]}):
        print(name)
    print("\nforeign_items")
    for name in sorted({name for row in rows for name in row["foreign_items_reached"]}):
        print(name)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
