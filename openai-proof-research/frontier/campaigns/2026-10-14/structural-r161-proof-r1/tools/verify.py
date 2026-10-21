#!/usr/bin/env python3
"""Read-only exact selected-payload verifier; no mathematical verdict.
Usage: python verify.py ROOT FINAL_SHA256 MANIFEST_SHA256 REPORT_SHA256
"""
import hashlib
import json
import os
from pathlib import Path
import stat
import sys
ENVELOPES = ('FINAL.md','MANIFEST.json','REPORT.md')
SCHEMA = 'structural-r161-proof-r1-selected-v1'

def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
    return h.hexdigest()

def regular(p):
    st=p.lstat()
    if not stat.S_ISREG(st.st_mode) or st.st_nlink != 1:
        raise ValueError('not a regular single-link file: '+str(p))
    return st

def inventory(root):
    if root.is_symlink() or not root.is_dir():raise ValueError('invalid root')
    files={};directories={}
    for base,ds,fs in os.walk(root,topdown=True,followlinks=False):
        for name in ds:
            p=Path(base)/name;st=p.lstat()
            if not stat.S_ISDIR(st.st_mode):raise ValueError('not a real directory: '+str(p))
            directories[p.relative_to(root).as_posix()]=oct(stat.S_IMODE(st.st_mode))
        for name in fs:
            p=Path(base)/name;st=regular(p);rel=p.relative_to(root).as_posix()
            if rel not in ENVELOPES:
                files[rel]={'size':st.st_size,'sha256':sha(p),'mode':oct(stat.S_IMODE(st.st_mode))}
    return {'files':dict(sorted(files.items())),'directories':dict(sorted(directories.items()))}

def verify(root,anchors):
    if len(anchors)!=3:raise ValueError('three detached anchors are required')
    for name,anchor in zip(ENVELOPES,anchors):
        p=root/name;regular(p)
        if len(anchor)!=64 or sha(p)!=anchor:raise ValueError('detached anchor mismatch: '+name)
    data=json.loads((root/'MANIFEST.json').read_text())
    if data.get('schema')!=SCHEMA:raise ValueError('unknown schema')
    actual=inventory(root)
    if actual['files']!=data['files']:raise ValueError('file membership, bytes or mode mismatch')
    if actual['directories']!=data['directories']:raise ValueError('directory membership or mode mismatch')
    return True

def main():
    if len(sys.argv)!=5:raise ValueError('need root and FINAL/MANIFEST/REPORT detached SHA256 anchors')
    verify(Path(sys.argv[1]),sys.argv[2:])
    print('ARTIFACT VERIFIED: exact selected payload membership, bytes and modes; three detached anchors match. This is not a mathematical gate.')

if __name__=='__main__':
    try:main()
    except Exception as exc:
        print('ARTIFACT REJECTED: '+str(exc));sys.exit(1)
