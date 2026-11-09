#!/usr/bin/env python3
"""Read-only exact packet verifier. Detached anchors must be supplied explicitly."""
import argparse, hashlib, json, os, stat
from pathlib import Path, PurePosixPath

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def safe(s):
    p=PurePosixPath(s)
    assert not p.is_absolute() and s==p.as_posix() and s not in ('','.','..')
    assert '..' not in p.parts
    return s

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--base',required=True)
    ap.add_argument('--final-sha256',required=True)
    ap.add_argument('--manifest-sha256',required=True)
    ap.add_argument('--report-sha256',required=True)
    a=ap.parse_args();base=Path(a.base)
    assert base.is_dir() and not base.is_symlink(), 'invalid base'
    assert stat.S_IMODE(base.stat().st_mode)==0o700, 'base mode'
    for name,anchor in [('FINAL.md',a.final_sha256),('MANIFEST.json',a.manifest_sha256),('REPORT.md',a.report_sha256)]:
        p=base/name
        assert p.is_file() and not p.is_symlink(), 'missing/symlink anchor: '+name
        assert sha(p)==anchor, 'detached anchor mismatch: '+name
    m=json.loads((base/'MANIFEST.json').read_text())
    assert m['schema']=='r215-exact-packet-v1'
    entries=m['entries'];expected={safe(e['path']) for e in entries}
    assert len(expected)==len(entries), 'duplicate selection'
    assert 'FINAL.md' in expected and 'MANIFEST.json' not in expected and 'REPORT.md' not in expected
    outside={safe(x) for x in m['outside_files']};outside_dirs={safe(x) for x in m['outside_directories']}
    assert not expected & outside
    actual=set();dirs=set()
    for root,ds,fs in os.walk(base,topdown=True,followlinks=False):
        rel=Path(root).relative_to(base).as_posix()
        assert stat.S_IMODE(Path(root).stat().st_mode)==0o700, 'directory mode: '+rel
        keep=[]
        for d in ds:
            p=Path(root)/d;s=p.relative_to(base).as_posix()
            assert not p.is_symlink(), 'symlink directory: '+s
            if s not in outside_dirs:keep.append(d);dirs.add(s)
        ds[:]=keep
        for f in fs:
            p=Path(root)/f;s=p.relative_to(base).as_posix()
            assert p.is_file() and not p.is_symlink(), 'nonregular file: '+s
            assert stat.S_IMODE(p.stat().st_mode)==0o600, 'file mode: '+s
            if s not in outside:actual.add(s)
    assert actual==expected, 'exact selection differs: '+repr(sorted(actual^expected))
    assert dirs==set(m['directories']), 'directory selection differs'
    for e in entries:
        p=base/e['path']
        assert p.stat().st_size==e['bytes'], 'size mismatch: '+e['path']
        assert stat.S_IMODE(p.stat().st_mode)==int(e['mode'],8), 'manifest mode: '+e['path']
        assert sha(p)==e['sha256'], 'hash mismatch: '+e['path']
    print(json.dumps({'artifact_integrity':'verified','selected_files':len(entries),'selected_bytes':sum(e['bytes'] for e in entries),'mathematical_gate':False}))

if __name__=='__main__':
    try:main()
    except (AssertionError,KeyError,ValueError,OSError) as e:
        raise SystemExit('ARTIFACT VERIFICATION FAILED: '+str(e))
