#!/usr/bin/env python3
"""Explore ALU statement interleavings from passively sampled PicoRV32 inputs."""

import hashlib
from pathlib import Path
import sys
import tempfile

import e_run_input_check as core


REPLAY = core.ROOT / "harness/rv/picorv32_preemption.lean"


def write_monitor(path: Path, signals: list[str]) -> None:
    if not signals or len(set(signals)) != len(signals) or not all(s.isidentifier() for s in signals):
        raise ValueError(f"invalid ALU signal list: {signals}")
    displays = "\n".join(
        f'    $display("SNAP %0d %b {s} %b", tb.cycle, post, tb.dut.{s});'
        for s in signals
    )
    path.write_text(f"""`timescale 1ns/1ps
module alu_snapshot;
  tb_picorv32_rvfi_long tb();
  task snapshot(input bit post);
{displays}
  endtask
  always @(posedge tb.clk) if (tb.cycle == 12 || tb.cycle == 28) begin
    snapshot(0);
    #0.5 snapshot(1);
  end
endmodule
""")


def main() -> None:
    for source, digest in [(core.SOURCE, core.SOURCE_SHA256), (core.TESTBENCH, core.TESTBENCH_SHA256)]:
        if hashlib.sha256(source.read_bytes()).hexdigest() != digest:
            raise ValueError(f"pinned hash mismatch for {source.name}")
    core.run(["lake", "build", "LeanModels.Sv.Kernel.CoreMemResume", "LeanModels.Sv.Ingest2"], core.ROOT)
    with tempfile.TemporaryDirectory(prefix="picorv32-preemption-") as directory:
        work = Path(directory)
        envelope = work / "retained.json"
        core.run([sys.executable, core.ROOT / "extractors/sv/extract.py", "--top", "picorv32",
                  "-D", "RISCV_FORMAL", "--retain-proc-rewrites", "-o", envelope, core.SOURCE], work)
        lean = ["lake", "env", "lean", "--run", REPLAY]
        signals = core.run([*lean, "signals", envelope], core.ROOT).splitlines()
        monitor = work / "snapshot.sv"
        write_monitor(monitor, signals)
        sources = [core.SOURCE, core.TESTBENCH, monitor]
        for command, pin in [(["iverilog", "-V"], core.ICARUS_PIN), (["xrun", "-version"], core.XCELIUM_PIN)]:
            version = core.run(command, work).splitlines()[0]
            if pin not in version:
                raise ValueError(f"unexpected simulator version: {version}")
            print(version, flush=True)
        core.run(["iverilog", "-g2012", "-DRISCV_FORMAL", "-s", "alu_snapshot", "-o", "bench", *sources], work)
        core.run(["xrun", "-elaborate", "-sv", "-q", "-define", "RISCV_FORMAL", "-top", "alu_snapshot",
                  *sources], work)
        # addi x1,x0,5; addi x2,x0,5; beq x1,x2,+8; addi x5,x0,99; ebreak.
        (work / "branch.hex").write_text("00500093\n00500113\n00208463\n06300293\n00100073\n")
        samples = []
        for cycle, args in [(12, ["+image=branch.hex"]), (28, [])]:
            records = []
            for sim in [["vvp", "bench"], ["xrun", "-R", "-q"]]:
                output = core.run([*sim, *args], work)
                records.append([s for s in output.splitlines() if s.startswith(f"SNAP {cycle} ")])
            if records[0] != records[1] or len(records[0]) != 2 * len(signals):
                raise ValueError(f"cycle {cycle}: incomplete or differing simulator snapshots")
            path = work / f"cycle-{cycle}.snap"
            path.write_text("\n".join(records[0]) + "\n")
            samples.append(path)
        print(core.run([*lean, "replay", envelope, *samples], core.ROOT), end="")


if __name__ == "__main__":
    main()
