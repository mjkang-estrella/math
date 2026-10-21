#!/usr/bin/env python3
"""Read-only integrity verification; not a mathematical or contribution gate.
Usage: python -B verify.py ROOT FINAL_SHA256 MANIFEST_SHA256 REPORT_SHA256
"""
import hashlib,json,os,stat,sys
from pathlib import Path
ENVELOPES=('FINAL.md','MANIFEST.json','REPORT.md')
SCHEMA='structural-r161-contribution-r1-exact-v1'
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def inventory(root):
    if root.is_symlink() or not root.is_dir():
        raise ValueError('root is not a real directory')
    files={};directories={}
    for base,ds,fs in os.walk(root,topdown=True,followlinks=False):
        for name in ds:
            p=Path(base)/name;s=p.lstat()
            if not stat.S_ISDIR(s.st_mode):raise ValueError('non-directory or symlink: '+str(p))
            directories[p.relative_to(root).as_posix()]=stat.S_IMODE(s.st_mode)
        for name in fs:
            p=Path(base)/name;s=p.lstat();rel=p.relative_to(root).as_posix()
            if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1:raise ValueError('not regular single-link: '+rel)
            if rel in ENVELOPES:continue
            files[rel]={'size':s.st_size,'mode':stat.S_IMODE(s.st_mode),'sha256':sha(p)}
    return {'directories':dict(sorted(directories.items())),'files':dict(sorted(files.items()))}
def verify(root,anchors):
    root=Path(root)
    if len(anchors)!=3:raise ValueError('three detached anchors required')
    for name,anchor in zip(ENVELOPES,anchors):
        p=root/name;s=p.lstat()
        if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1:raise ValueError('invalid envelope '+name)
        if len(anchor)!=64 or sha(p)!=anchor:raise ValueError('detached anchor mismatch: '+name)
    manifest=json.loads((root/'MANIFEST.json').read_text())
    if manifest.get('schema')!=SCHEMA:raise ValueError('schema mismatch')
    actual=inventory(root)
    if actual['directories']!=manifest['directories']:raise ValueError('directory membership/mode mismatch')
    if actual['files']!=manifest['files']:raise ValueError('file membership/bytes/mode mismatch')
if __name__=='__main__':
    try:
        if len(sys.argv)!=5:raise ValueError('usage: ROOT FINAL_SHA256 MANIFEST_SHA256 REPORT_SHA256')
        verify(sys.argv[1],sys.argv[2:])
        print('INTEGRITY MATCH: exact payload, modes and three detached envelopes; no mathematical gate.')
    except Exception as exc:
        print('INTEGRITY MISMATCH: '+str(exc));sys.exit(1)
