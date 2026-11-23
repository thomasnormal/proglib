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
 with tempfile.TemporaryDirectory(prefix='sv-comb-chain-') as d:
  out=Path(d)/'e.json'; run(['python3','extractors/sv/extract.py','--retain-proc-rewrites','--top','comb_chain_unpacked','-o',str(out),str((HERE/'comb_chain_unpacked.sv').relative_to(ROOT))]); assert out.read_bytes()==(HERE/'comb_chain_unpacked.sv.json').read_bytes()
  exe=Path(d)/'sim'; run(['iverilog','-g2012','-s','comb_chain_unpacked_tb','-o',str(exe),str(HERE/'comb_chain_unpacked.sv'),str(HERE/'comb_chain_unpacked_tb.sv')],d); got=rows(run([str(exe)],d)); print('Icarus Verilog 13.0:',len(got),'rows')
  if shutil.which('xrun'):
   with tempfile.TemporaryDirectory(prefix='sv-xcelium-comb-chain-') as w: x=rows(run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','comb_chain_unpacked_tb',str(HERE/'comb_chain_unpacked.sv'),str(HERE/'comb_chain_unpacked_tb.sv')],w))
   print('Xcelium 24.03-s004:',len(x),'rows MATCH' if x==got else 'rows DIVERGE')
  else: print('Xcelium 24.03-s004: unavailable')
 print('ordinary E: source-shaped genvar chain admitted')
if __name__=='__main__': main()
