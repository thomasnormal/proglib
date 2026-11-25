#!/usr/bin/env python3
from pathlib import Path
import json, shutil, subprocess, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
def run(args, cwd=ROOT):
    p = subprocess.run(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=180)
    if p.returncode:
        raise RuntimeError(p.stdout)
    return p.stdout
def main():
    with tempfile.NamedTemporaryFile(suffix='.json') as f:
        run(['python3','extractors/sv/extract.py','--top',HERE.name,'-o',f.name,
             str((HERE/(HERE.name+'.sv')).relative_to(ROOT))])
        if Path(f.name).read_bytes() != (HERE/(HERE.name+'.sv.json')).read_bytes():
            raise RuntimeError('stale envelope')
    census = run(['python3','harness/sv/refusal_census.py','ordinary',
                   str(HERE/(HERE.name+'.sv.json'))])
    if 'active generate declarations contain duplicate names' not in census:
        raise RuntimeError(f'expected duplicate-scope refusal, got {census}')
    run(['lake','env','lean',str(HERE/'agree.lean')])
    print('ordinary E: explicit duplicate-active-generate-scope refusal')
    tb = '''module tb; logic [1:0] i; wire [1:0] o;
 duplicate_generate_group_e dut(.i(i),.o(o));
 initial begin i=2'b00; #1 $display("ROW 00 %b",o); i=2'b11; #1 $display("ROW 11 %b",o); i=2'bxx; #1 $display("ROW xx %b",o); i=2'bzz; #1 $display("ROW zz %b",o); $finish; end endmodule
'''
    src = str(HERE/(HERE.name+'.sv'))
    for sim in ['iverilog'] + (['xrun'] if shutil.which('xrun') else []):
        with tempfile.TemporaryDirectory(prefix='sv-duplicate-generate-group-') as w:
            tb_path = Path(w)/'tb.sv'; tb_path.write_text(tb)
            if sim == 'iverilog':
                exe = str(Path(w)/'sim')
                result = subprocess.run(['iverilog','-g2012','-s','tb','-o',exe,src,str(tb_path)], cwd=w, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                version = run(['iverilog','-V'],w).splitlines()[0]
            else:
                result = subprocess.run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','tb',src,str(tb_path)], cwd=w, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                version = run(['xrun','-version'],w).splitlines()[0]
        if result.returncode == 0:
            raise RuntimeError(f'{sim}: simulator unexpectedly accepted duplicate scope')
        print(f'{version}: source rejected duplicate active scope (no oracle rows claimed)')
if __name__ == '__main__': main()
