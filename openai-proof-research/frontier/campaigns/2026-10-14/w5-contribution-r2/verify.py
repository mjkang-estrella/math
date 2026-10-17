#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang. No affiliation.
"""Read-only, externally anchored identity check; not a mathematical oracle."""
import argparse, hashlib, json, pathlib, subprocess, sys

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--anchor',required=True)
    ap.add_argument('--repo',type=pathlib.Path)
    ap.add_argument('--dependencies',action='store_true')
    args=ap.parse_args()
    here=pathlib.Path(__file__).resolve().parent
    repo=args.repo.resolve() if args.repo else here.parents[3]
    manifest=here/'manifest.json'
    assert sha(manifest)==args.anchor, 'external manifest anchor mismatch'
    m=json.loads(manifest.read_text())
    entries=list(here.rglob('*'))
    assert not any(p.is_symlink() for p in entries), 'symlink forbidden'
    actual={p.relative_to(here).as_posix() for p in entries if p.is_file() and p!=manifest}
    assert actual==set(m['files']), 'exact file membership mismatch'
    dirs=sorted(p.relative_to(here).as_posix() for p in entries if p.is_dir())
    assert dirs==m['directories'], 'exact directory membership mismatch'
    for name,rec in m['files'].items():
        p=here/name
        assert p.stat().st_size==rec['size'] and sha(p)==rec['sha256'], 'payload changed: '+name
    inputs=json.loads((here/'input-hashes.json').read_text())
    for name,rec in inputs.items():
        p=repo/name
        assert p.stat().st_size==rec['size'] and sha(p)==rec['sha256'], 'external input changed: '+name
    if args.dependencies:
        a=repo/'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r25'
        p=subprocess.run([sys.executable,'-B',str(a/'verify.py'),'--anchor',m['author_anchor']],capture_output=True,text=True)
        assert p.returncode==0, 'author dependency verification failed: '+p.stdout+p.stderr
    print(json.dumps({'status':'IDENTITY_VERIFIED_NOT_MATHEMATICAL_VERDICT','payloads':len(actual),'directories':len(dirs),'inputs':len(inputs),'author_dependency_replayed':args.dependencies}))

if __name__=='__main__':
    try: main()
    except Exception as e:
        print('VERIFICATION_FAILED: '+str(e),file=sys.stderr)
        sys.exit(1)
