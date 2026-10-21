#!/usr/bin/env python3
"""Read-only exact-membership and detached-envelope checker; no mathematical gate."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat

ENVELOPES = ('FINAL.md', 'MANIFEST.json', 'REPORT.md')

def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''):
            h.update(block)
    return h.hexdigest()

def inventory(root):
    root=Path(root)
    if root.is_symlink() or not root.is_dir():
        raise ValueError('root must be an actual directory')
    records=[]; directories=[]
    for base, ds, fs in os.walk(root,followlinks=False):
        ds.sort(); fs.sort()
        for name in ds:
            p=Path(base)/name
            if p.is_symlink(): raise ValueError('symlink directory: '+str(p))
            directories.append(p.relative_to(root).as_posix())
        for name in fs:
            p=Path(base)/name
            rel=p.relative_to(root).as_posix()
            st=p.lstat()
            if not stat.S_ISREG(st.st_mode): raise ValueError('nonregular file: '+rel)
            if rel in ENVELOPES: continue
            records.append(dict(path=rel,bytes=st.st_size,mode=stat.S_IMODE(st.st_mode),sha256=sha(p)))
    return sorted(records,key=lambda x:x['path']),sorted(directories)

def check_payload(root,records,directories):
    seen=set()
    for r in records:
        n=r['path']; p=PurePosixPath(n)
        if p.is_absolute() or '..' in p.parts or p.as_posix()!=n or n in ENVELOPES or n in seen:
            raise ValueError('invalid or duplicate payload path')
        seen.add(n)
    actual,actual_dirs=inventory(root)
    if actual != sorted(records,key=lambda x:x['path']):
        raise ValueError('payload membership, bytes, mode, or hash mismatch')
    if actual_dirs != sorted(directories) or len(set(directories))!=len(directories):
        raise ValueError('directory membership mismatch')
    return len(actual)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',type=Path,default=Path(__file__).absolute().parent)
    ap.add_argument('--final-sha256',required=True)
    ap.add_argument('--manifest-sha256',required=True)
    ap.add_argument('--report-sha256',required=True)
    args=ap.parse_args()
    for name,expected in zip(ENVELOPES,(args.final_sha256,args.manifest_sha256,args.report_sha256)):
        if len(expected)!=64 or any(c not in '0123456789abcdef' for c in expected):
            raise ValueError('detached hash must be lowercase SHA256')
        p=args.root/name
        if p.is_symlink() or not p.is_file() or sha(p)!=expected:
            raise ValueError('detached envelope mismatch: '+name)
    m=json.loads((args.root/'MANIFEST.json').read_text())
    if m.get('schema')!='arithmetic-r136-contribution-r1/v1':
        raise ValueError('unexpected manifest schema')
    n=check_payload(args.root,m['payload'],m['directories'])
    print(json.dumps(dict(exact_membership=True,payload_files=n,envelopes=3,meaning='artifact integrity only; no mathematical verdict'),sort_keys=True))

if __name__=='__main__':
    main()
