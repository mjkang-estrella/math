#!/usr/bin/env python3
"""Read-only byte/membership check; all three detached anchors are mandatory."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath

WRAPPERS = {'FINAL.md', 'MANIFEST.json', 'REPORT.md', 'ANCHORS.json'}

def digest(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda: f.read(1024 * 1024), b''):
            h.update(b)
    return h.hexdigest()

def files(root):
    found = set()
    for base, dirs, names in os.walk(root, followlinks=False):
        for name in dirs + names:
            if (Path(base) / name).is_symlink():
                raise ValueError('symlink in packet')
        for name in names:
            rel = (Path(base) / name).relative_to(root).as_posix()
            if rel not in WRAPPERS:
                found.add(rel)
    return found

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', required=True, type=Path)
    p.add_argument('--final-sha256', required=True)
    p.add_argument('--manifest-sha256', required=True)
    p.add_argument('--report-sha256', required=True)
    a = p.parse_args()
    root = a.root.resolve(strict=True)
    for name, expected in [('FINAL.md', a.final_sha256),
                           ('MANIFEST.json', a.manifest_sha256),
                           ('REPORT.md', a.report_sha256)]:
        if len(expected) != 64 or any(c not in '0123456789abcdef' for c in expected):
            raise ValueError('invalid explicit SHA256 anchor')
        if (root / name).is_symlink() or digest(root / name) != expected:
            raise ValueError('detached anchor mismatch: ' + name)
    m = json.loads((root / 'MANIFEST.json').read_text(encoding='utf-8'))
    if m['format'] != 'r174-exact-packet-v1' or set(m['excluded_wrappers']) != WRAPPERS:
        raise ValueError('manifest format mismatch')
    seen = set()
    for row in m['files']:
        rel = row['path']; pp = PurePosixPath(rel)
        if not rel or pp.is_absolute() or '..' in pp.parts or pp.as_posix() != rel:
            raise ValueError('noncanonical manifest path')
        if rel in WRAPPERS or rel in seen:
            raise ValueError('duplicate or wrapper payload path')
        seen.add(rel)
        f = root / rel
        if f.is_symlink() or not f.is_file() or f.stat().st_size != row['bytes']:
            raise ValueError('payload file/size mismatch: ' + rel)
        if digest(f) != row['sha256']:
            raise ValueError('payload hash mismatch: ' + rel)
    if seen != files(root):
        raise ValueError('exact payload membership mismatch')
    print(json.dumps({'artifact_integrity': 'matched', 'payload_files': len(seen),
                      'mathematical_gate': False}))

if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError, json.JSONDecodeError) as exc:
        raise SystemExit(str(exc))
