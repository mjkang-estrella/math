#!/usr/bin/env python3
"""Read-only exact release-preparation inventory verification; not a research verdict."""
import argparse, hashlib, json, stat
from pathlib import Path

def check(root, anchor):
    files=[]; dirs=[]
    def walk(p):
        rel=p.relative_to(root).as_posix(); s=p.lstat()
        if stat.S_ISDIR(s.st_mode):
            dirs.append(rel)
            for q in sorted(p.iterdir()): walk(q)
        elif stat.S_ISREG(s.st_mode):
            assert s.st_nlink==1, 'hardlink'
            assert p.name!='manifest.json' or rel=='manifest.json', 'nested manifest'
            files.append(rel)
        else: raise AssertionError('nonregular node')
    walk(root)
    raw=(root/'manifest.json').read_bytes()
    assert hashlib.sha256(raw).hexdigest()==anchor, 'external anchor mismatch'
    m=json.loads(raw); names=[e['path'] for e in m['files']]
    assert len(names)==len(set(names)), 'duplicate path'
    assert all(n not in ('','.','manifest.json') and not Path(n).is_absolute() and '..' not in Path(n).parts and Path(n).as_posix()==n for n in names), 'unsafe path'
    assert sorted(files)==sorted(names+['manifest.json']), 'file inventory'
    assert sorted(dirs)==m['directories'], 'directory inventory'
    for e in m['files']:
        b=(root/e['path']).read_bytes()
        assert len(b)==e['bytes'] and hashlib.sha256(b).hexdigest()==e['sha256'], 'payload mismatch: '+e['path']
    return {'status':'PASS_PREPARATION_SEAL_IDENTITY_ONLY','payloads':len(names),'directories':len(dirs)}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--expected-manifest-sha256',required=True);p.add_argument('--root',type=Path);a=p.parse_args()
    print(json.dumps(check(a.root.absolute() if a.root else Path(__file__).absolute().parent,a.expected_manifest_sha256)))
