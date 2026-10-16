#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT License.
"""Rejection tests on disposable copies; never alter frozen originals."""
import argparse
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
ROOT=Path(__file__).resolve().parent
sys.dont_write_bytecode=True

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seal-sha256',required=True);a=ap.parse_args()
    # Authenticate the original package using the frozen verifier before copying.
    r=subprocess.run([sys.executable,'-B',str(ROOT/'verify.py'),'--seal-sha256',a.seal_sha256],stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
    assert b'PASS_INTEGRITY_AND_FINITE_SUPPORT_ONLY_H_UNRESOLVED' in r.stdout
    originals={p.relative_to(ROOT).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in ROOT.rglob('*') if p.is_file()}
    with tempfile.TemporaryDirectory(prefix='.mutation-disposable-',dir=ROOT) as td:
        d=Path(td)
        for trial in ['code','receipt','input','extra','manifest']:
            c=d/trial;c.mkdir()
            for name in originals:
                dest=c/name;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/name,dest);dest.chmod(0o600)
            sentinel=c/'EXECUTED_SENTINEL'
            badcode="from pathlib import Path\nPath(__file__).with_name('EXECUTED_SENTINEL').write_text('BAD')\n"
            if trial=='code':(c/'checks.py').write_text(badcode+(c/'checks.py').read_text())
            elif trial=='receipt':(c/'checks-receipt.txt').write_bytes(b'changed\n')
            elif trial=='input':(c/'inputs/private/upstream/paper.tex').write_bytes(b'changed\n')
            elif trial=='extra':(c/'unexpected-file.txt').write_text('extra\n')
            else:(c/'outputs-manifest.json').write_text('{}\n')
            z=subprocess.run([sys.executable,'-B',str(c/'verify.py'),'--seal-sha256',a.seal_sha256],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
            assert z.returncode!=0 and not sentinel.exists()
            assert b'AUTHENTICATED ' not in z.stdout
            print('REJECTED_BEFORE_EXECUTION '+trial)
    after={p.relative_to(ROOT).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in ROOT.rglob('*') if p.is_file()}
    assert originals==after
    print('PASS_5_AUTHENTICATION_MUTATIONS_ORIGINALS_UNCHANGED')
if __name__=='__main__':main()
