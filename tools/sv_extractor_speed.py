#!/usr/bin/env python3
"""Measure extractor time on the package/generate hierarchy wall.

The source is deliberately parser-shaped and is kept here so the speed
measurement does not depend on a generated envelope or a private design.
"""

from pathlib import Path
import os
import subprocess
import tempfile
import time


ROOT = Path(__file__).resolve().parents[1]
SOURCE = """package cfg;
  parameter int unsigned N = 32;
endpackage
module leaf #(parameter int unsigned W = cfg::N)
  (input logic [W-1:0] i, output logic [W-1:0] o);
  assign o = i;
endmodule
module top;
  for (genvar k = 0; k < cfg::N; k++) begin : g
    leaf u (.i('0), .o());
  end
endmodule
"""


def main():
    tmp_root = os.environ.get("TMPDIR")
    if not tmp_root:
        raise SystemExit("set TMPDIR to a scratch directory")
    with tempfile.TemporaryDirectory(dir=tmp_root, prefix="sv-extractor-speed-") as directory:
        directory = Path(directory)
        source = directory / "wall.sv"
        envelope = directory / "wall.sv.json"
        source.write_text(SOURCE)
        started = time.monotonic()
        subprocess.run([
            "python3", "extractors/sv/extract.py", "--top", "top",
            "-o", str(envelope), str(source),
        ], cwd=ROOT, check=True)
        elapsed = time.monotonic() - started
    print(f"package/generate hierarchy extraction: {elapsed:.3f}s")


if __name__ == "__main__":
    main()
