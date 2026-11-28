#!/usr/bin/env python3
from pathlib import Path
import subprocess, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
def run(cmd):
    p = subprocess.run(cmd, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
    if p.returncode: raise RuntimeError(p.stdout)
    return p.stdout
def main():
    with tempfile.NamedTemporaryFile(suffix='.json') as f:
        run(['python3','extractors/sv/extract.py','--top','signed_packed_array_target_e','-o',f.name,str(HERE/'signed_packed_array_target_e.sv')])
        if Path(f.name).read_bytes() != (HERE/'signed_packed_array_target_e.sv.json').read_bytes(): raise RuntimeError('stale envelope')
    run(['lake','env','lean',str(HERE/'agree.lean')])
    print('ordinary memory route: signed packed-array target refusal MATCH')
    print('No simulator value row claimed because the ordinary route refuses before execution.')
if __name__ == '__main__': main()
