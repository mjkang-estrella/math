#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Externally anchored file identity only; not a mathematical proof checker."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath

def sha(b): return hashlib.sha256(b).hexdigest()
def need(ok, why):
    if not ok: raise ValueError(why)

def main():
    p=argparse.ArgumentParser(); p.add_argument('--anchor',required=True); a=p.parse_args()
    root=Path(__file__).resolve().parent
    raw=(root/'manifest.json').read_bytes()
    need(sha(raw)==a.anchor,'external manifest anchor mismatch')
    m=json.loads(raw); names=set()
    for e in m['files']:
        n=e['path']; q=PurePosixPath(n)
        need(not q.is_absolute() and str(q)==n and '..' not in q.parts and n not in names and n!='manifest.json','unsafe/duplicate path')
        names.add(n); b=(root/n).read_bytes()
        need(len(b)==e['bytes'] and sha(b)==e['sha256'],'payload '+n)
    files=set(); dirs=set()
    for q in root.rglob('*'):
        need(not q.is_symlink(),'symlink')
        n=q.relative_to(root).as_posix()
        if q.is_dir(): dirs.add(n)
        else:
            need(q.is_file(),'special file'); files.add(n)
    need(files==names|{'manifest.json'} and dirs==set(m['directories']),'membership mismatch')
    sources=json.loads((root/'source-receipt.json').read_text())
    for e in sources:
        b=(root/e['local']).read_bytes()
        need(len(b)==e['bytes'] and sha(b)==e['sha256'],'source identity')
        need(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob'],'Git blob')
    primary=json.loads((root/'primary-receipt.json').read_text())
    for e in primary:
        b=(root/e['path']).read_bytes()
        need(b.startswith(b'%PDF') and len(b)==e['bytes'] and sha(b)==e['sha256'],'primary identity')
    print(json.dumps(dict(status='INTEGRITY_ONLY',payloads=len(names),pinned_blobs=len(sources),primary_pdfs=len(primary),count_change=0)))

if __name__=='__main__':
    try: main()
    except (ValueError,KeyError,OSError,TypeError) as e: raise SystemExit('REJECT: '+str(e))
