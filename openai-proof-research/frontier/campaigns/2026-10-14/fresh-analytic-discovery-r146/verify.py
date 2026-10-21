#!/usr/bin/env python3
"""Read-only exact-byte/membership verification; detached anchors are mandatory.
This is artifact verification, not mathematical validation. No writes/imports of
packet code, network access, original-manifest inheritance, or seal refresh.
"""
import argparse,hashlib,json,os
from pathlib import Path,PurePosixPath
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
def digest(b):return hashlib.sha256(b).hexdigest()
def files(root):
    found={}
    if root.is_symlink() or not root.is_dir():raise ValueError('root must be a real directory')
    for base,dirs,names in os.walk(root,followlinks=False):
        for name in dirs+names:
            p=Path(base)/name
            if p.is_symlink():raise ValueError('symlink: '+str(p.relative_to(root)))
        for name in names:
            p=Path(base)/name
            if not p.is_file():raise ValueError('nonregular file')
            found[str(p.relative_to(root))]=p
    return found

def verify(root,anchors):
    actual=files(root)
    for name,anchor in anchors.items():
        if len(anchor)!=64 or any(c not in '0123456789abcdef' for c in anchor):raise ValueError('invalid anchor')
        if name not in actual or digest(actual[name].read_bytes())!=anchor:raise ValueError('detached anchor: '+name)
    manifest=json.loads(actual['MANIFEST.json'].read_text())
    if manifest.get('schema')!='r146-exact-payload-v1':raise ValueError('schema')
    expected={}
    for rec in manifest['files']:
        name=rec['path'];p=PurePosixPath(name)
        if p.is_absolute() or '..' in p.parts or str(p)!=name or name in ENVELOPES or name in expected:raise ValueError('unsafe/duplicate payload path')
        expected[name]=rec
    if set(actual)!=set(expected)|ENVELOPES:raise ValueError('exact membership mismatch')
    for name,rec in expected.items():
        b=actual[name].read_bytes()
        if len(b)!=rec['size'] or digest(b)!=rec['sha256']:raise ValueError('payload mismatch: '+name)
    return len(expected)
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',required=True)
    p.add_argument('--final-sha256',required=True)
    p.add_argument('--manifest-sha256',required=True)
    p.add_argument('--report-sha256',required=True)
    a=p.parse_args()
    try:
        count=verify(Path(a.root),{'FINAL.md':a.final_sha256,'MANIFEST.json':a.manifest_sha256,'REPORT.md':a.report_sha256})
    except Exception as e:
        print('REJECT:',e);raise SystemExit(1)
    print(f'ACCEPT: {count} payload files and exactly three anchored envelopes; artifact bytes only')
