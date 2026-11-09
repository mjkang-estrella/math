#!/usr/bin/env python3
"""MIT. Deliberate integrity controls, confined to new disposable copies."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--packet',type=Path,required=True)
    ap.add_argument('--scratch',type=Path,required=True)
    ap.add_argument('--expect-finalhash',required=True)
    args=ap.parse_args()
    root=args.packet.resolve(); scratch=args.scratch.absolute()
    if scratch.exists() or root==scratch or root in scratch.parents:
        raise ValueError('scratch must be new and outside packet')
    scratch.mkdir(parents=True)
    verifier=root/'public/verify.py'; results=[]
    def run(name, mutate=None, anchor=None, omit=False, expected=1):
        dst=scratch/name; shutil.copytree(root,dst)
        if mutate: mutate(dst)
        before={p.relative_to(dst).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in dst.rglob('*') if p.is_file() and not p.is_symlink()}
        cmd=[sys.executable,'-B',str(verifier),'--packet',str(dst)]
        if not omit: cmd+=['--expect-finalhash',anchor or args.expect_finalhash]
        p=subprocess.run(cmd,capture_output=True,text=True,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
        after={p.relative_to(dst).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in dst.rglob('*') if p.is_file() and not p.is_symlink()}
        ok=(p.returncode==0) if expected==0 else (p.returncode!=0)
        if before!=after: raise AssertionError('verifier wrote files')
        if not ok: raise AssertionError(name+': unexpected result '+p.stdout+p.stderr)
        results.append(dict(case=name,expected='accept' if expected==0 else 'reject',returncode=p.returncode,verifier_read_only=True,output=(p.stdout+p.stderr).strip()))
    run('baseline',expected=0)
    run('missing-anchor',omit=True)
    run('wrong-anchor',anchor='0'*64)
    run('modified-report',lambda p:(p/'public/research-report.md').write_text('changed\n'))
    run('missing-file',lambda p:(p/'public/status.json').unlink())
    run('extra-file',lambda p:(p/'unexpected').write_text('extra\n'))
    run('extra-directory',lambda p:(p/'empty-extra').mkdir())
    def symlink(p):
        q=p/'public/status.json'; q.unlink(); q.symlink_to('research-report.md')
    run('symlink',symlink)
    def hardlink(p):
        q=p/'public/status.json'; q.unlink(); os.link(p/'public/research-report.md',q)
    run('hardlink',hardlink)
    run('changed-source',lambda p:(p/'private/upstream/types.tex').write_text('changed source\n'))
    run('changed-primary',lambda p:(p/'private/primary/cff-v3.pdf').write_bytes(b'%PDF-changed'))
    run('modified-manifest',lambda p:(p/'manifest.json').write_text('{}\n'))
    run('changed-mode',lambda p:(p/'public/status.json').chmod(0o600))
    # Even a self-consistent replacement inventory cannot satisfy the original detached anchor.
    def reseal(p):
        q=p/'public/status.json'; q.write_text('{}\n'); m=json.loads((p/'manifest.json').read_text())
        for row in m['files']:
            if row['path']=='public/status.json': row['bytes']=3; row['sha256']=hashlib.sha256(q.read_bytes()).hexdigest()
        (p/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
    run('resealed-mutation',reseal)
    print(json.dumps(dict(finalhash=args.expect_finalhash,controls=results,integrity_only=True),indent=2))
if __name__=='__main__': main()
