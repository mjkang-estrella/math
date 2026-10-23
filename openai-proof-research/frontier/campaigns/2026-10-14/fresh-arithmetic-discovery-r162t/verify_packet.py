#!/usr/bin/env python3
"""Read-only exact-packet verification with caller-supplied detached anchors."""
import argparse, hashlib, json, stat
from pathlib import Path, PurePosixPath

def digest(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''): h.update(block)
    return h.hexdigest()

def main():
    a=argparse.ArgumentParser()
    for name in ('packet','manifest','final','report','manifest-sha256','final-sha256','report-sha256'):
        a.add_argument('--'+name,required=True)
    v=a.parse_args()
    for name in ('manifest','final','report'):
        p=Path(getattr(v,name))
        assert not p.is_symlink() and p.is_file(), 'nonregular detached '+name
        assert digest(p)==getattr(v,name+'_sha256'), 'detached hash mismatch: '+name
    root=Path(v.packet)
    assert root.is_dir() and not root.is_symlink(), 'invalid packet root'
    m=json.loads(Path(v.manifest).read_text())
    assert m['schema']=='exact-packet-v1'
    expected={}
    for e in m['files']:
        rel=e['path']; q=PurePosixPath(rel)
        assert rel==q.as_posix() and not q.is_absolute() and '..' not in q.parts and rel not in expected, 'invalid manifest path'
        expected[rel]=e
    actual={}; dirs=[]
    for p in root.rglob('*'):
        assert not p.is_symlink(), 'symlink in packet'
        rel=p.relative_to(root).as_posix()
        if p.is_dir(): dirs.append(rel)
        else:
            assert p.is_file(), 'nonregular packet entry'
            actual[rel]=p
    assert sorted(actual)==sorted(expected), 'packet file set mismatch'
    assert sorted(dirs)==m['directories'], 'packet directory set mismatch'
    for rel,p in actual.items():
        e=expected[rel]
        assert p.stat().st_size==e['bytes'], 'size mismatch: '+rel
        assert stat.S_IMODE(p.stat().st_mode)==e['mode'], 'mode mismatch: '+rel
        assert digest(p)==e['sha256'], 'content mismatch: '+rel
    print(json.dumps({'artifact_verification':'PASS','files':len(actual),'mathematical_gate':False}))

if __name__=='__main__':
    main()
