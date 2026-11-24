#!/usr/bin/env python3
from pathlib import Path
import shutil, subprocess, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = ["ROW 0000 1111", "ROW 0101 1010", "ROW xxxx xxxx"]
def run(cmd, cwd=ROOT):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120)
    if p.returncode:
        raise RuntimeError(p.stdout)
    return p.stdout
def main():
    with tempfile.NamedTemporaryFile(suffix='.json') as f:
        run(['python3','extractors/sv/extract.py','--retain-proc-rewrites','--top',HERE.name,'-o',f.name,str(HERE/(HERE.name+'.sv'))])
        if f.read() != (HERE/(HERE.name+'.sv.json')).read_bytes(): raise RuntimeError('stale envelope')
    run(['lake','env','lean',str(HERE/'agree.lean')])
    print('extractor: envelope regenerates byte-identically')
    print('E: 3 rows MATCH: 1111, 1010, xxxx')
    with tempfile.TemporaryDirectory(prefix='sv-e-assign-user-function-') as w:
        exe = str(Path(w)/'sim')
        run(['iverilog','-g2012','-s','assign_calls_user_function_e_tb','-o',exe,str(HERE/(HERE.name+'.sv')),str(HERE/(HERE.name+'_tb.sv'))], w)
        rows = [x for x in run([exe], w).splitlines() if x.startswith('ROW ')]
        if rows != EXPECTED: raise RuntimeError(f'Icarus rows {rows} != {EXPECTED}')
    print('Icarus Verilog 13.0: 3 rows MATCH E')
    if shutil.which('xrun'):
        with tempfile.TemporaryDirectory(prefix='sv-xcelium-assign-user-function-') as w:
            out = run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','assign_calls_user_function_e_tb',str(HERE/(HERE.name+'.sv')),str(HERE/(HERE.name+'_tb.sv'))], w)
        rows = [x for x in out.splitlines() if x.startswith('ROW ')]
        if rows != EXPECTED: raise RuntimeError(f'Xcelium rows {rows} != {EXPECTED}')
        print('Xcelium 24.03-s004: 3 rows MATCH E')
    else:
        print('no Xcelium result: xrun unavailable')
if __name__ == '__main__': main()
