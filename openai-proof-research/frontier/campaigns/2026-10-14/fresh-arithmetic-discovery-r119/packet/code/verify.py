#!/usr/bin/env python3
"""Read-only exact-membership verifier. External SHA256 anchors are mandatory."""
import argparse, hashlib, json, os, stat
from pathlib import Path

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def regular(p):
    s=p.lstat()
    if not stat.S_ISREG(s.st_mode) or s.st_nlink != 1:
        raise ValueError('nonregular, symlink, or multiply linked file: '+str(p))

def verify(root, anchors):
    if root.is_symlink() or not root.is_dir():
        raise ValueError('root must be a real directory')
    for name,anchor in anchors.items():
        regular(root/name)
        if len(anchor)!=64 or digest(root/name)!=anchor:
            raise ValueError('detached anchor mismatch: '+name)
    manifest=json.loads((root/'MANIFEST.json').read_text())
    if manifest.get('schema')!='r119-exact-v1':
        raise ValueError('unknown manifest schema')
    expected=manifest['files']; dirs=manifest['directories']
    names=[e['path'] for e in expected]
    if len(set(names))!=len(names) or set(names)&set(anchors):
        raise ValueError('duplicate or envelope payload entry')
    for name in names+dirs:
        p=Path(name)
        if p.is_absolute() or '..' in p.parts or p.as_posix()!=name:
            raise ValueError('invalid relative path')
    gotfiles=[];gotdirs=[]
    for base,subdirs,files in os.walk(root,followlinks=False):
        for name in subdirs:
            p=Path(base)/name
            if p.is_symlink() or not stat.S_ISDIR(p.lstat().st_mode):
                raise ValueError('non-directory/symlink entry')
            gotdirs.append(p.relative_to(root).as_posix())
        for name in files:
            p=Path(base)/name;regular(p)
            gotfiles.append(p.relative_to(root).as_posix())
    if set(gotfiles)!=set(names)|set(anchors) or len(gotfiles)!=len(names)+3:
        raise ValueError('exact file membership mismatch')
    if sorted(gotdirs)!=sorted(dirs) or len(set(dirs))!=len(dirs):
        raise ValueError('exact directory membership mismatch')
    for e in expected:
        p=root/e['path']
        if p.stat().st_size!=e['size'] or digest(p)!=e['sha256']:
            raise ValueError('payload mismatch: '+e['path'])
    return len(names),len(dirs)

def main():
    a=argparse.ArgumentParser()
    a.add_argument('--root',required=True)
    a.add_argument('--final-sha256',required=True)
    a.add_argument('--manifest-sha256',required=True)
    a.add_argument('--report-sha256',required=True)
    x=a.parse_args()
    try:
        n,d=verify(Path(x.root),{'FINAL.md':x.final_sha256,'MANIFEST.json':x.manifest_sha256,'REPORT.md':x.report_sha256})
    except (ValueError,OSError,KeyError,TypeError) as e:
        raise SystemExit('FAIL: '+str(e))
    print(f'OK: {n} payloads, 3 independently anchored envelopes, {d} directories; bytes and membership only')
if __name__=='__main__':
    main()
