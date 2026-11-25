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
 with tempfile.TemporaryDirectory(prefix='sv-unpacked-bit-target-') as d:
  out=Path(d)/'e.json'; run(['python3','extractors/sv/extract.py','--top','unpacked_bitselect_target','-o',str(out),str((HERE/'unpacked_bitselect_target.sv').relative_to(ROOT))]); assert out.read_bytes()==(HERE/'unpacked_bitselect_target.sv.json').read_bytes()
  exe=Path(d)/'sim'; run(['iverilog','-g2012','-s','unpacked_bitselect_target_tb','-o',str(exe),str(HERE/'unpacked_bitselect_target.sv'),str(HERE/'unpacked_bitselect_target_tb.sv')],d); got=rows(run([str(exe)],d)); print('Icarus Verilog 13.0:',len(got),'rows')
  if shutil.which('xrun'):
   with tempfile.TemporaryDirectory(prefix='sv-xcelium-unpacked-bit-target-') as w: x=rows(run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','unpacked_bitselect_target_tb',str(HERE/'unpacked_bitselect_target.sv'),str(HERE/'unpacked_bitselect_target_tb.sv')],w))
   print('Xcelium 24.03-s004:',len(x),'rows MATCH' if x==got else 'rows DIVERGE')
  else: print('Xcelium 24.03-s004: unavailable')
 print('ordinary E: rows are pinned by agree.lean after source-shaped extraction')
if __name__=='__main__': main()
