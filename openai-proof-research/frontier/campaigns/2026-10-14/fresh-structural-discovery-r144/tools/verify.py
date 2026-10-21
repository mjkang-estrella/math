#!/usr/bin/env python3
"""Read-only packet verification. External detached anchors are mandatory."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re

OUTER = frozenset({'MANIFEST.json', 'FINAL.md', 'REPORT.md', 'ANCHORS.sha256'})
FORBIDDEN = re.compile(r'analytic.*r13[5678]|t177c143-|structural.*r143|arithmetic.*r10[789]|t373e135-|k369r134-|t088p133-', re.I)

def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1048576), b''):
            h.update(block)
    return h.hexdigest()

def safe_name(name):
    p = Path(name)
    if not name or p.is_absolute() or '..' in p.parts or str(p) != name:
        raise ValueError('Unsafe manifest path: ' + name)
    if any(FORBIDDEN.search(c) for c in p.parts):
        raise ValueError('Excluded component: ' + name)

def inventory(root):
    files, directories = set(), set()
    for base, ds, fs in os.walk(root, followlinks=False):
        for n in list(ds):
            p = Path(base) / n
            rel = p.relative_to(root).as_posix()
            if FORBIDDEN.search(n):
                ds.remove(n)  # prune BEFORE descent; fail closed without opening
                raise ValueError('Excluded directory present: ' + rel)
            if p.is_symlink():
                ds.remove(n)
                raise ValueError('Symlink directory: ' + rel)
            directories.add(rel)
        for n in fs:
            rel = (Path(base) / n).relative_to(root).as_posix()
            safe_name(rel)
            p = root / rel
            if p.is_symlink() or not p.is_file():
                raise ValueError('Non-regular file: ' + rel)
            files.add(rel)
    return files, directories

def check_payload(root, records, directories, outer=OUTER):
    names = [r['path'] for r in records]
    if len(names) != len(set(names)):
        raise ValueError('Duplicate manifest path')
    for name in names:
        safe_name(name)
        if name in outer:
            raise ValueError('Outer file in payload: ' + name)
    for name in directories:
        safe_name(name)
    files, actual_dirs = inventory(root)
    if files != set(names) | set(outer):
        raise ValueError('File membership differs; missing=' + str(sorted((set(names) | set(outer))-files)) + '; extra=' + str(sorted(files-(set(names) | set(outer)))))
    if actual_dirs != set(directories):
        raise ValueError('Directory membership differs')
    for r in records:
        p = root / r['path']
        if p.stat().st_size != r['bytes'] or digest(p) != r['sha256']:
            raise ValueError('Payload differs: ' + r['path'])

def check_anchor(path, expected):
    if not re.fullmatch('[0-9a-f]{64}', expected):
        raise ValueError('Invalid detached SHA256')
    if path.is_symlink() or not path.is_file() or digest(path) != expected:
        raise ValueError('Detached anchor mismatch: ' + path.name)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('root', type=Path)
    ap.add_argument('--manifest-sha256', required=True)
    ap.add_argument('--final-sha256', required=True)
    ap.add_argument('--report-sha256', required=True)
    args = ap.parse_args()
    root = args.root.resolve()
    anchors = {'MANIFEST.json': args.manifest_sha256, 'FINAL.md': args.final_sha256, 'REPORT.md': args.report_sha256}
    for name, expected in anchors.items():
        check_anchor(root/name, expected)
    m = json.loads((root/'MANIFEST.json').read_text())
    if m['schema'] != 'r144-exact-payload-v1' or set(m['outer_files']) != OUTER:
        raise ValueError('Unexpected manifest schema or outer files')
    check_payload(root, m['files'], m['directories'])
    expected_text = ''.join(anchors[name] + '  ' + name + '\n' for name in ['MANIFEST.json','FINAL.md','REPORT.md'])
    if (root/'ANCHORS.sha256').read_text() != expected_text:
        raise ValueError('Detached anchor record differs from supplied anchors')
    print('Packet bytes and exact membership verified. No mathematical verdict.')

if __name__ == '__main__':
    main()
