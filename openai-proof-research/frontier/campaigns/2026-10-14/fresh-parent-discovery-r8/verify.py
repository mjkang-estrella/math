#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang
"""Read-only exact inventory/source identity check. No mathematical certification."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
SCOPE='bb115b9c504b9e5d8e3f62d841bc16095049f23719a47eb13d18d253ed1741c5'
def sha(x):return hashlib.sha256(x).hexdigest()
def need(b,s):
    if not b:raise ValueError(s)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--anchor',required=True);a=ap.parse_args()
    root=Path(__file__).resolve().parent
    raw=(root/'manifest.json').read_bytes();need(sha(raw)==a.anchor,'external manifest anchor mismatch');m=json.loads(raw)
    names=set();dirs=set();actual=set()
    for row in m['files']:
        n=row['path'];p=PurePosixPath(n)
        need(not p.is_absolute() and p.as_posix()==n and '..' not in p.parts and n not in names and n!='manifest.json','unsafe/duplicate path')
        names.add(n);raw=(root/n).read_bytes();need(len(raw)==row['bytes'] and sha(raw)==row['sha256'],'payload '+n)
    for p in root.rglob('*'):
        need(not p.is_symlink(),'symlink');n=p.relative_to(root).as_posix()
        if p.is_dir():dirs.add(n)
        else:need(p.is_file(),'special file');actual.add(n)
    need(actual==names|{'manifest.json'},'exact file membership');need(dirs==set(m['directories']),'exact directory membership')
    need(sha((root/'original-scope.md').read_bytes())==SCOPE,'scope')
    tree=json.loads((root/'family-inventory.json').read_text());need(tree['pin']==PIN and tree['tree_truncated'] is False,'source pin/tree')
    blobs={r['path']:r['sha'] for r in tree['entries'] if r['type']=='blob'}
    sr=json.loads((root/'source-receipt.json').read_text())
    for r in sr:
        raw=(root/r['local']).read_bytes();need(sha(raw)==r['sha256'] and len(raw)==r['bytes'],'source bytes')
        need(hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==r['git_blob']==blobs[r['path']],'source Git blob')
    pr=json.loads((root/'private/primary-receipt.json').read_text())
    for r in pr:
        raw=(root/'private'/r['file']).read_bytes();need(raw.startswith(b'%PDF') and len(raw)==r['bytes'] and sha(raw)==r['sha256'],'primary PDF')
    print(json.dumps(dict(result='IDENTITY_ONLY',payloads=len(names),pinned_text_blobs=len(sr),primary_PDFs=len(pr),scope_sha256=SCOPE,mathematical_code_executed=False,writes=0,count_changed=False)))
if __name__=='__main__':
    try:main()
    except (ValueError,KeyError,OSError,TypeError) as e:raise SystemExit('REJECT: '+str(e))
