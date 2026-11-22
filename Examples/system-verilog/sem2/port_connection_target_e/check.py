#!/usr/bin/env python3
from pathlib import Path
import json, subprocess, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
ENV = HERE / 'port_connection_target_e.sv.json'
rows = subprocess.run(['python3','harness/sv/refusal_census.py','ordinary',str(ENV)], cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE).stdout
if '"refusals": 0' not in rows:
    raise SystemExit(rows)
TB = '''module tb; logic d; logic [3:0] y; register_parent dut(.d(d),.y(y)); initial begin d=0; #1 $display("ROW %b",y); d=1; #1 $display("ROW %b",y); d=1'bx; #1 $display("ROW %b",y); d=1'bz; #1 $display("ROW %b",y); $finish; end endmodule'''
expected = [['0000'], ['1111'], ['xxxx'], ['zzzz']]
for sim in ('iverilog','xrun'):
    with tempfile.TemporaryDirectory(prefix='sv-port-target-e-') as td:
        tb = Path(td) / 'tb.sv'; tb.write_text(TB)
        if sim == 'iverilog':
            exe = Path(td) / 'sim'
            proc = subprocess.run(['iverilog','-g2012','-s','tb','-o',str(exe),str(HERE/'port_connection_target_e.sv'),str(tb)], cwd=td, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if proc.returncode == 0:
                raise SystemExit('iverilog unexpectedly accepted unpacked aggregate structs')
            print('iverilog: source refusal (unpacked structs unsupported)')
            continue
        out = subprocess.run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','tb',str(HERE/'port_connection_target_e.sv'),str(tb)], cwd=td, check=True, text=True, stdout=subprocess.PIPE).stdout
        actual = [line.split()[1:] for line in out.splitlines() if line.startswith('ROW ')]
        if actual != expected:
            raise SystemExit(f'{sim}: {actual} != {expected}')
        print('xrun: 4 rows MATCH')
