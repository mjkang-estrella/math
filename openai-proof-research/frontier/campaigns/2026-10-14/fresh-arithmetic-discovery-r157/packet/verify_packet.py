#!/usr/bin/env python3
"""Read-only artifact verification; all detached anchors are required explicitly."""
import argparse,hashlib,json,stat
from pathlib import Path,PurePosixPath

def digest(b):return hashlib.sha256(b).hexdigest()
def verify(root,final_anchor,manifest_anchor,report_anchor):
    root=Path(root);packet=root/'packet'
    for name,anchor in [('packet/FINAL.md',final_anchor),('MANIFEST.json',manifest_anchor),('REPORT.json',report_anchor)]:
        assert len(anchor)==64 and all(c in '0123456789abcdef' for c in anchor),'invalid explicit anchor'
        p=root/name
        assert not p.is_symlink(),f'symlink: {name}'
        assert digest(p.read_bytes())==anchor,f'anchor mismatch: {name}'
    manifest=json.loads((root/'MANIFEST.json').read_bytes())
    report=json.loads((root/'REPORT.json').read_bytes())
    assert report['manifest_sha256']==manifest_anchor,'report manifest binding'
    assert report['final_sha256']==final_anchor,'report final binding'
    entries=manifest['files'];expected=set();total=0
    for e in entries:
        rel=PurePosixPath(e['path'])
        assert not rel.is_absolute() and '..' not in rel.parts and str(rel)==e['path'],'unsafe path'
        assert e['path'] not in expected,'duplicate path'
        expected.add(e['path']);p=packet/rel
        assert p.is_file() and not p.is_symlink(),f'missing/nonregular: {rel}'
        b=p.read_bytes();assert len(b)==e['bytes'],f'size mismatch: {rel}'
        assert digest(b)==e['sha256'],f'content mismatch: {rel}'
        assert stat.S_IMODE(p.stat().st_mode)==e['mode'],f'mode mismatch: {rel}'
        total+=len(b)
    actual=set()
    for p in packet.rglob('*'):
        assert not p.is_symlink(),f'symlink: {p}'
        if p.is_file():actual.add(p.relative_to(packet).as_posix())
    assert actual==expected,f'file set mismatch: extra={sorted(actual-expected)} missing={sorted(expected-actual)}'
    return f'MATCH: {len(expected)} packet files, {total} bytes; artifact integrity only'

if __name__=='__main__':
    a=argparse.ArgumentParser(description=__doc__)
    a.add_argument('root');a.add_argument('--final-sha256',required=True);a.add_argument('--manifest-sha256',required=True);a.add_argument('--report-sha256',required=True)
    v=a.parse_args();print(verify(v.root,v.final_sha256,v.manifest_sha256,v.report_sha256))
