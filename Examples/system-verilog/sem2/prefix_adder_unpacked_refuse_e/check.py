#!/usr/bin/env python3
from pathlib import Path
import subprocess,tempfile,shutil
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3]
def run(a,cwd=ROOT):
 p=subprocess.run(a,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180);return p.returncode,p.stdout
def main():
 with tempfile.NamedTemporaryFile(suffix='.json') as f:
  rc,out=run(['python3','extractors/sv/extract.py','--top',HERE.name,'-o',f.name,str((HERE/(HERE.name+'.sv')).relative_to(ROOT))])
  if rc or Path(f.name).read_bytes()!=(HERE/(HERE.name+'.sv.json')).read_bytes(): raise RuntimeError(out)
 rc,out=run(['python3','harness/sv/refusal_census.py','ordinary',str(HERE/(HERE.name+'.sv.json'))])
 if '"refusals": 0' not in out: raise RuntimeError(out)
 rc,out=run(['lake','env','lean',str(HERE/'agree.lean')])
 if rc: raise RuntimeError(out)
 print('ordinary E: generated unpacked bit targets admitted, 4 rows MATCH')
 tb='''module tb; logic [3:0] a; wire [3:0] y; prefix_adder_unpacked_refuse_e dut(a,y); initial begin a=4'b0000;#1 $display("ROW 0000 %b",y);a=4'b0011;#1 $display("ROW 0011 %b",y);a=4'bxxxx;#1 $display("ROW xxxx %b",y);a=4'bzzzz;#1 $display("ROW zzzz %b",y);$finish;end endmodule'''
 for sim in ['iverilog']+(['xrun'] if shutil.which('xrun') else []):
  with tempfile.TemporaryDirectory(prefix='sv-prefix-unpacked-refuse-') as w:
   src=str(HERE/(HERE.name+'.sv')); p=Path(w)/'tb.sv';p.write_text(tb)
   if sim=='iverilog':
    rc,out=run(['iverilog','-g2012','-s','tb','-o',str(Path(w)/'sim'),src,str(p)],w); ver=run(['iverilog','-V'],w)[1].splitlines()[0]
    if rc==0: rc,out=run(['vvp',str(Path(w)/'sim')],w)
   else: rc,out=run(['xrun','-sv','-q','-top','tb',src,str(p)],w);ver=run(['xrun','-version'],w)[1].splitlines()[0]
  if rc: raise RuntimeError(f'{sim}: {out}')
  actual=[x for x in out.splitlines() if x.startswith('ROW ')]
  expected=['ROW 0000 0000','ROW 0011 0011','ROW xxxx xxxx','ROW zzzz zzzz']
  if actual != expected: raise RuntimeError(f'{sim}: {actual!r}')
  print(f'{ver}: 4 rows MATCH E')
if __name__=='__main__':main()
