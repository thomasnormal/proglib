#!/usr/bin/env python3
from pathlib import Path
import subprocess,tempfile,shutil
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
def run(args,cwd=ROOT):
 p=subprocess.run(args,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
 return p.returncode,p.stdout
def main():
 with tempfile.NamedTemporaryFile(suffix='.json') as f:
  rc,out=run(['python3','extractors/sv/extract.py','--top','datapath','-o',f.name,str((HERE/(HERE.name+'.sv')).relative_to(ROOT))])
  if rc or Path(f.name).read_bytes()!=(HERE/(HERE.name+'.sv.json')).read_bytes(): raise RuntimeError(out)
 rc,out=run(['python3','harness/sv/refusal_census.py','ordinary',str(HERE/(HERE.name+'.sv.json'))])
 if 'SlangError:InvalidSelectExpression' not in out: raise RuntimeError(out)
 rc,out=run(['lake','env','lean',str(HERE/'agree.lean')])
 if rc: raise RuntimeError(out)
 print('ordinary E: explicit SlangError:InvalidSelectExpression refusal')
 for sim in ['iverilog']+(['xrun'] if shutil.which('xrun') else []):
  with tempfile.TemporaryDirectory(prefix='sv-shift-add-refuse-') as w:
   src=str(HERE/(HERE.name+'.sv'))
   if sim=='iverilog': rc,out=run(['iverilog','-g2012','-s','datapath','-o',str(Path(w)/'sim'),src],w); ver=run(['iverilog','-V'],w)[1].splitlines()[0]
   else: rc,out=run(['xrun','-sv','-q','-top','datapath',src],w); ver=run(['xrun','-version'],w)[1].splitlines()[0]
  if rc==0: raise RuntimeError(f'{sim} unexpectedly accepted source')
  print(f'{ver}: source rejected before simulation (no oracle rows claimed)')
if __name__=='__main__': main()
