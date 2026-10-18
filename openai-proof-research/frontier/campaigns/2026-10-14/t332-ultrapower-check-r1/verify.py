#!/usr/bin/env python3
"""MIT. Read-only exact inventory check; no proof verdict."""
import argparse, hashlib, json, stat, sys
from pathlib import Path

def check(root,anchor):
    files=[]; dirs=[]
    def walk(p,rel):
        s=p.lstat()
        if stat.S_ISDIR(s.st_mode):
            dirs.append(rel)
            for q in sorted(p.iterdir()): walk(q,q.relative_to(root).as_posix())
        elif stat.S_ISREG(s.st_mode):
            if s.st_nlink!=1: raise ValueError('hardlink: '+rel)
            if p.name=='MANIFEST.json' and rel!='MANIFEST.json': raise ValueError('nested manifest')
            files.append(rel)
        else: raise ValueError('link or nonregular: '+rel)
    walk(root,'.')
    raw=(root/'MANIFEST.json').read_bytes()
    if hashlib.sha256(raw).hexdigest()!=anchor: raise ValueError('external anchor mismatch')
    m=json.loads(raw); names=[e['path'] for e in m['files']]
    if len(names)!=len(set(names)) or sorted(names+['MANIFEST.json'])!=sorted(files): raise ValueError('file inventory mismatch')
    if m['directories']!=sorted(dirs): raise ValueError('directory inventory mismatch')
    for e in m['files']:
        b=(root/e['path']).read_bytes()
        if len(b)!=e['bytes'] or hashlib.sha256(b).hexdigest()!=e['sha256']: raise ValueError('payload mismatch: '+e['path'])
    return {'status':'PASS','payload_files':len(names),'directories':len(dirs),'scope':'Evidence identity only; author-side check, no independent mathematical gate.'}

def main():
    p=argparse.ArgumentParser();p.add_argument('--expected-manifest-sha256',required=True);p.add_argument('--root',type=Path);a=p.parse_args()
    root=a.root.absolute() if a.root else Path(__file__).absolute().parent
    print(json.dumps(check(root,a.expected_manifest_sha256)))
if __name__=='__main__':
    try:main()
    except Exception as e: print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
