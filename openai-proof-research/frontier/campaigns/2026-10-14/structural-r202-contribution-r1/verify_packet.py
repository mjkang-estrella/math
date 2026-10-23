#!/usr/bin/env python3
"""Read-only verification of exact review files/directories, modes and explicit anchors."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat

OUTSIDE = {'FINAL.json', 'MANIFEST.json', 'REPORT.md', 'ANCHORS.txt'}

def digest(b):
    return hashlib.sha256(b).hexdigest()

def require(condition, message):
    if not condition:
        raise ValueError(message)

def safe(root, name):
    p = PurePosixPath(name)
    require(not p.is_absolute() and p.parts and all(x not in ('', '.', '..') for x in p.parts), 'invalid path')
    q = root
    for part in p.parts:
        q = q / part
        require(not q.is_symlink(), 'symlink: ' + name)
    return q

def mode(q):
    return format(stat.S_IMODE(q.stat().st_mode), '04o')

def verify(root, final_sha, manifest_sha, report_sha):
    root = Path(root).absolute()
    require(root.is_dir() and not root.is_symlink(), 'invalid root')
    expected = {'FINAL.json': final_sha, 'MANIFEST.json': manifest_sha, 'REPORT.md': report_sha}
    raw = {}
    for name, sha in expected.items():
        require(len(sha) == 64 and all(c in '0123456789abcdef' for c in sha), 'explicit SHA256 required')
        raw[name] = safe(root, name).read_bytes()
        require(digest(raw[name]) == sha, 'detached anchor mismatch: ' + name)
    m = json.loads(raw['MANIFEST.json'])
    f = json.loads(raw['FINAL.json'])
    require(m['format'] == 'structural-r202-contribution-r1-packet-v1', 'manifest format')
    require(set(m['outside_modes']) == OUTSIDE, 'outside selection')
    require(f['manifest_sha256'] == manifest_sha and f['report_sha256'] == report_sha, 'FINAL cross-bindings')
    names = [e['path'] for e in m['files']]
    dnames = [e['path'] for e in m['directories']]
    require(len(names) == len(set(names)) and not set(names) & OUTSIDE, 'selected file duplicates/outside')
    require(len(dnames) == len(set(dnames)) and '.' in dnames, 'directory selection')
    actual_files, actual_dirs = set(), {'.'}
    for here, dirs, files in os.walk(root, followlinks=False):
        for name in dirs + files:
            q = Path(here) / name
            require(not q.is_symlink(), 'symlink in packet')
        for name in dirs:
            actual_dirs.add((Path(here) / name).relative_to(root).as_posix())
        for name in files:
            q = Path(here) / name
            require(stat.S_ISREG(q.stat().st_mode), 'nonregular file')
            actual_files.add(q.relative_to(root).as_posix())
    require(actual_files == set(names) | OUTSIDE, 'exact file set differs')
    require(actual_dirs == set(dnames), 'exact directory set differs')
    for e in m['directories']:
        q = root if e['path'] == '.' else safe(root, e['path'])
        require(q.is_dir() and mode(q) == e['mode'], 'directory mode/type: ' + e['path'])
    for e in m['files']:
        q = safe(root, e['path'])
        b = q.read_bytes()
        require(mode(q) == e['mode'], 'file mode: ' + e['path'])
        require(len(b) == e['bytes'] and digest(b) == e['sha256'], 'file bytes: ' + e['path'])
    for name, wanted in m['outside_modes'].items():
        require(mode(safe(root, name)) == wanted, 'outside mode: ' + name)
    require(f['review_path'] in names, 'review not selected')
    require(digest(safe(root, f['review_path']).read_bytes()) == f['review_sha256'], 'review binding')
    anchors = ''.join(name + ' ' + sha + '\n' for name, sha in expected.items())
    require(safe(root, 'ANCHORS.txt').read_text() == anchors, 'ANCHORS differs from explicit arguments')
    return {'artifact_verified': True, 'read_only': True, 'selected_files': len(names), 'directories': len(dnames), 'outside_files': len(OUTSIDE)}

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', default=str(Path(__file__).absolute().parent))
    p.add_argument('--final-sha256', required=True)
    p.add_argument('--manifest-sha256', required=True)
    p.add_argument('--report-sha256', required=True)
    a = p.parse_args()
    try:
        print(json.dumps(verify(a.root, a.final_sha256, a.manifest_sha256, a.report_sha256), sort_keys=True))
        return 0
    except (ValueError, OSError, KeyError, TypeError) as exc:
        print('ARTIFACT REJECTED:', str(exc))
        return 1

if __name__ == '__main__':
    raise SystemExit(main())
