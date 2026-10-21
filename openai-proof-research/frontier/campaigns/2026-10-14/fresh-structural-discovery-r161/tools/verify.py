#!/usr/bin/env python3
"""Read-only artifact verifier. Requires three independently supplied SHA256 anchors.
Usage: python verify.py ROOT FINAL_SHA256 MANIFEST_SHA256 REPORT_SHA256
This checks bytes/membership, not mathematics; it never writes target files.
"""
import hashlib,json,os,stat,sys
from pathlib import Path
ENVELOPES=('FINAL.md','MANIFEST.json','REPORT.md')
def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def inventory(root):
    if root.is_symlink() or not root.is_dir():raise ValueError('root must be a real directory')
    files={};directories=[]
    for base,ds,fs in os.walk(root,topdown=True,followlinks=False):
        for n in ds:
            p=Path(base)/n
            if not stat.S_ISDIR(p.lstat().st_mode):raise ValueError('non-directory/symlink: '+str(p))
            directories.append(p.relative_to(root).as_posix())
        for n in fs:
            p=Path(base)/n;info=p.lstat()
            if not stat.S_ISREG(info.st_mode) or info.st_nlink!=1:raise ValueError('not regular single-link: '+str(p))
            rel=p.relative_to(root).as_posix()
            if rel not in ENVELOPES:files[rel]={'size':info.st_size,'sha256':sha(p)}
    return {'directories':sorted(directories),'files':dict(sorted(files.items()))}
def main():
    if len(sys.argv)!=5:raise ValueError('need root and explicit FINAL/MANIFEST/REPORT SHA256 anchors')
    root=Path(sys.argv[1])
    for name,anchor in zip(ENVELOPES,sys.argv[2:]):
        p=root/name;info=p.lstat()
        if not stat.S_ISREG(info.st_mode) or info.st_nlink!=1:raise ValueError('invalid envelope '+name)
        if len(anchor)!=64 or sha(p)!=anchor:raise ValueError('detached anchor mismatch: '+name)
    expected=json.loads((root/'MANIFEST.json').read_text())
    if expected.get('schema')!='r161-exact-payload-v1':raise ValueError('unknown manifest schema')
    actual=inventory(root)
    if actual['directories']!=expected['directories']:raise ValueError('directory membership mismatch')
    if actual['files']!=expected['files']:raise ValueError('payload membership/bytes mismatch')
    print('ARTIFACT ACCEPT: exact payload bytes and membership; three detached anchors matched. No mathematical gate.')
if __name__=='__main__':
    try:main()
    except Exception as e:
        print('ARTIFACT REJECT: '+str(e));sys.exit(1)
