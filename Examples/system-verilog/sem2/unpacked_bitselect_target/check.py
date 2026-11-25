#!/usr/bin/env python3
from pathlib import Path
import shutil, subprocess, tempfile
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
def run(cmd,cwd=ROOT):
 p=subprocess.run(cmd,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120)
 if p.returncode: raise RuntimeError(p.stdout)
 return p.stdout
def rows(s): return [x for x in s.splitlines() if x.startswith('ROW ')]
def main():
 expected=['ROW a=0 b=0 y=0','ROW a=a b=3 y=9','ROW a=x b=5 y=x','ROW a=z b=5 y=x']
 with tempfile.TemporaryDirectory(prefix='sv-unpacked-bit-target-') as d:
  out=Path(d)/'e.json'; run(['python3','extractors/sv/extract.py','--top','unpacked_bitselect_target','-o',str(out),str((HERE/'unpacked_bitselect_target.sv').relative_to(ROOT))]); assert out.read_bytes()==(HERE/'unpacked_bitselect_target.sv.json').read_bytes()
  exe=Path(d)/'sim'; run(['iverilog','-g2012','-s','unpacked_bitselect_target_tb','-o',str(exe),str(HERE/'unpacked_bitselect_target.sv'),str(HERE/'unpacked_bitselect_target_tb.sv')],d); got=rows(run([str(exe)],d)); assert got==expected; print('Icarus Verilog 13.0: 4 rows MATCH E outputs')
  if shutil.which('xrun'):
   with tempfile.TemporaryDirectory(prefix='sv-xcelium-unpacked-bit-target-') as w: x=rows(run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','unpacked_bitselect_target_tb',str(HERE/'unpacked_bitselect_target.sv'),str(HERE/'unpacked_bitselect_target_tb.sv')],w))
   assert x==expected; print('Xcelium 24.03-s004: 4 rows MATCH E outputs')
  else: print('Xcelium 24.03-s004: unavailable')
 print('ordinary E: rows are pinned by agree.lean after source-shaped extraction')
if __name__=='__main__': main()
