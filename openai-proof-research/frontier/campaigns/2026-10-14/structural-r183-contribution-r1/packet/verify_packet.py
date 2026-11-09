#!/usr/bin/env python3
"""Read-only exact-packet and explicit detached-anchor verification.
Artifact checks only: no mathematical verdict. No writes or peer traversal.
Run from the actual project root; optional --check-inputs uses exact admitted paths.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat

def digest(b):
    return hashlib.sha256(b).hexdigest()

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha_arg(s):
    require(len(s) == 64 and all(c in '0123456789abcdef' for c in s), 'expected explicit lowercase SHA256')
    return s

def check(packet, report, final_sha, manifest_sha, report_sha, check_inputs=False):
    require(not packet.is_symlink() and packet.is_dir(), 'invalid packet directory')
    manifest = packet / 'MANIFEST.json'
    final = packet / 'FINAL.md'
    for p in [manifest, final, report]:
        require(p.is_file() and not p.is_symlink(), 'missing/symlink anchor: ' + str(p))
    require(digest(manifest.read_bytes()) == manifest_sha, 'MANIFEST anchor mismatch')
    require(digest(final.read_bytes()) == final_sha, 'FINAL anchor mismatch')
    require(digest(report.read_bytes()) == report_sha, 'REPORT anchor mismatch')
    m = json.loads(manifest.read_bytes())
    require(m['format'] == 's183n-contribution-r1-exact-packet-v1', 'manifest format')
    entries = m['files']
    names = set()
    for e in entries:
        name = e['path']
        rel = PurePosixPath(name)
        require(not rel.is_absolute() and '..' not in rel.parts and rel.as_posix() == name and '\\' not in name, 'unsafe member path')
        require(name != 'MANIFEST.json' and name not in names, 'duplicate/reserved member')
        names.add(name)
        p = packet / name
        require(p.is_file() and not p.is_symlink(), 'missing/symlink member: ' + name)
        b = p.read_bytes()
        require(len(b) == e['bytes'] and digest(b) == e['sha256'], 'member bytes mismatch: ' + name)
        require(stat.S_IMODE(p.stat().st_mode) == e['mode'], 'member mode mismatch: ' + name)
    actual = set()
    for base, dirs, files in os.walk(packet, followlinks=False):
        for name in dirs + files:
            require(not (Path(base)/name).is_symlink(), 'symlink in packet')
        for name in files:
            actual.add((Path(base)/name).relative_to(packet).as_posix())
    require(actual == names | {'MANIFEST.json'}, 'extra or missing packet member')
    require('FINAL.md' in names, 'FINAL absent from members')
    if check_inputs:
        expected_root = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
        require(Path.cwd() == expected_root, 'run --check-inputs from actual project root')
        footprint = json.loads((packet/'private/unchanged-inputs-before.json').read_bytes())
        for e in footprint:
            p = Path(e['path'])
            require(not p.is_absolute() and '..' not in p.parts, 'unsafe exact input')
            b = p.read_bytes()
            require(len(b) == e['bytes'] and digest(b) == e['sha256'], 'exact input changed: ' + str(p))
            require(stat.S_IMODE(p.stat().st_mode) == e['mode'], 'exact input mode changed: ' + str(p))
        for e in json.loads((packet/'private/author-metadata/history-extents.json').read_bytes()):
            with Path(e['path']).open('rb') as f:
                f.seek(e['start'])
                b = f.read(e['end'] - e['start'])
            require(digest(b) == e['sha256'], 'original history interval changed')
    return {'verified_members': len(entries), 'member_bytes':sum(e['bytes'] for e in entries),
            'explicit_detached_anchors_match':True,'exact_input_bytes_and_modes_checked':check_inputs,
            'mathematical_gate':False}

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--packet', required=True, type=Path)
    p.add_argument('--report', required=True, type=Path)
    p.add_argument('--final-sha', required=True, type=sha_arg)
    p.add_argument('--manifest-sha', required=True, type=sha_arg)
    p.add_argument('--report-sha', required=True, type=sha_arg)
    p.add_argument('--check-inputs', action='store_true')
    a = p.parse_args()
    try:
        result = check(a.packet,a.report,a.final_sha,a.manifest_sha,a.report_sha,a.check_inputs)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        p.exit(1,'REJECT: '+str(exc)+'\n')
    print(json.dumps(result,sort_keys=True))

if __name__ == '__main__':
    main()
