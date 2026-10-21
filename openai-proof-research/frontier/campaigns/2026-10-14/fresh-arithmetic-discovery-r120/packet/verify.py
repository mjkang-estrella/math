#!/usr/bin/env python3
"""Read-only exact research-packet verifier. No mathematical gate. Original code."""
import argparse, hashlib, json, os, stat
from pathlib import Path

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def inventory(root):
    files={}; directories=[]
    for base, ds, fs in os.walk(root, topdown=True, followlinks=False):
        for name in ds:
            p=Path(base)/name
            if not stat.S_ISDIR(p.lstat().st_mode) or p.is_symlink():
                raise ValueError('non-directory/symlink: '+str(p))
            directories.append(p.relative_to(root).as_posix())
        for name in fs:
            p=Path(base)/name; s=p.lstat()
            if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1:
                raise ValueError('nonregular/hardlink: '+str(p))
            files[p.relative_to(root).as_posix()]={'size':s.st_size,'sha256':digest(p)}
    return files,sorted(directories)

def verify(root,anchors):
    if root.is_symlink() or not root.is_dir(): raise ValueError('invalid root')
    for name, expected in anchors.items():
        p=root/name
        if p.is_symlink() or not p.is_file() or digest(p)!=expected:
            raise ValueError('detached anchor mismatch: '+name)
    m=json.loads((root/'MANIFEST.json').read_text())
    actual,dirs=inventory(root)
    expected=m['files']
    if set(actual)!=set(expected)|{'MANIFEST.json'}: raise ValueError('file membership mismatch')
    if dirs!=m['directories']: raise ValueError('directory membership mismatch')
    for name,record in expected.items():
        if actual[name]!=record: raise ValueError('payload mismatch: '+name)
    return {'artifact_only':True,'files':len(actual),'directories':len(dirs),'verified':True}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('root',type=Path)
    for flag in ('final','manifest','report'):p.add_argument('--'+flag+'-sha256',required=True)
    a=p.parse_args()
    try:
        print(json.dumps(verify(a.root,{'FINAL.md':a.final_sha256,'MANIFEST.json':a.manifest_sha256,'REPORT.md':a.report_sha256}),sort_keys=True))
    except (ValueError,OSError,KeyError,TypeError) as e:
        p.exit(1,'FAIL: '+str(e)+'\n')
