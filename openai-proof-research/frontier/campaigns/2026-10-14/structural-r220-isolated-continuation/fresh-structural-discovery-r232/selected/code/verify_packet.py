#!/usr/bin/env python3
"""Read-only exact-selection verifier. All three detached anchors are mandatory.
This checks artifact bytes/modes/selection, never mathematical correctness.
"""
import argparse, hashlib, json, os, stat
from pathlib import Path, PurePosixPath

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def require(ok, message):
    if not ok:
        raise ValueError(message)

def verify(root, final_sha, manifest_sha, report, report_sha):
    require(root.is_dir() and not root.is_symlink(), 'packet root is not an ordinary directory')
    require(digest(root/'FINAL.md') == final_sha, 'FINAL anchor mismatch')
    require(digest(root/'MANIFEST.json') == manifest_sha, 'MANIFEST anchor mismatch')
    require(report.is_file() and not report.is_symlink(), 'REPORT is not an ordinary file')
    require(digest(report) == report_sha, 'REPORT anchor mismatch')
    m = json.loads((root/'MANIFEST.json').read_text())
    expected = {'FINAL.md', 'MANIFEST.json'}
    for ent in m['files']:
        name = ent['path']; pp = PurePosixPath(name)
        require(not pp.is_absolute() and '..' not in pp.parts and str(pp) == name, 'invalid path')
        require(name not in expected, 'duplicate/reserved selected path')
        expected.add(name); p = root/name
        require(p.is_file() and not p.is_symlink(), 'selected file missing or symlink: '+name)
        require(p.stat().st_size == ent['bytes'], 'size mismatch: '+name)
        require(digest(p) == ent['sha256'], 'content mismatch: '+name)
        require(stat.S_IMODE(p.stat().st_mode) == int(ent['mode'],8), 'mode mismatch: '+name)
    for name in ['FINAL.md','MANIFEST.json']:
        require(stat.S_IMODE((root/name).stat().st_mode)==0o400, 'seal file mode mismatch')
    actual = set(); dirs = {'.'}
    for base, ds, fs in os.walk(root, followlinks=False):
        for d in ds:
            p=Path(base)/d
            require(not p.is_symlink(), 'directory symlink')
            dirs.add(p.relative_to(root).as_posix())
        for f in fs:
            p=Path(base)/f
            require(not p.is_symlink(), 'file symlink')
            actual.add(p.relative_to(root).as_posix())
    require(actual == expected, 'exact selection mismatch')
    require(dirs == set(m['directories']), 'directory selection mismatch')
    for d, mode in m['directories'].items():
        require(stat.S_IMODE((root/d).stat().st_mode)==int(mode,8), 'directory mode mismatch: '+d)
    return {'artifact_only': True, 'selected_files': len(m['files']), 'selected_bytes': sum(x['bytes'] for x in m['files']), 'exact_selection': True, 'modes': True, 'anchors': True}

if __name__ == '__main__':
    a=argparse.ArgumentParser(description=__doc__)
    a.add_argument('--root',required=True,type=Path)
    a.add_argument('--final-sha256',required=True)
    a.add_argument('--manifest-sha256',required=True)
    a.add_argument('--report',required=True,type=Path)
    a.add_argument('--report-sha256',required=True)
    x=a.parse_args()
    try:
        print(json.dumps(verify(x.root,x.final_sha256,x.manifest_sha256,x.report,x.report_sha256),sort_keys=True))
    except Exception as e:
        print(json.dumps({'artifact_only':True,'verified':False,'error':str(e)}))
        raise SystemExit(1)
