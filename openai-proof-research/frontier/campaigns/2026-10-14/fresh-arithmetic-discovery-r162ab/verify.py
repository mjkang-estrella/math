#!/usr/bin/env python3
"""Read-only exact-selection verifier; all three trusted anchors are explicit."""
import argparse
import hashlib
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True

EXCLUDED = {'MANIFEST.json', 'REPORT.md', 'ANCHORS.json'}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def verify(root, final_anchor, manifest_anchor, report_anchor):
    root = Path(root).resolve(strict=True)
    for name, anchor in [('FINAL.md', final_anchor), ('MANIFEST.json', manifest_anchor), ('REPORT.md', report_anchor)]:
        p = root / name
        if p.is_symlink() or sha(p.read_bytes()) != anchor:
            raise ValueError('detached anchor mismatch: ' + name)
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    entries = manifest['files']
    expected = set()
    for row in entries:
        name = row['path']
        rel = Path(name)
        if rel.is_absolute() or '..' in rel.parts or name in EXCLUDED or name in expected or rel.as_posix() != name:
            raise ValueError('invalid/duplicate selection path')
        expected.add(name)
        p = root / rel
        if p.is_symlink() or not p.is_file() or root not in p.resolve(strict=True).parents:
            raise ValueError('invalid selected file: ' + name)
        data = p.read_bytes()
        if len(data) != row['bytes'] or sha(data) != row['sha256']:
            raise ValueError('selected content mismatch: ' + name)
    actual = set()
    for p in root.rglob('*'):
        if p.is_symlink():
            raise ValueError('symlink in exact selection')
        if p.is_file():
            name = p.relative_to(root).as_posix()
            if name not in EXCLUDED:
                actual.add(name)
    if actual != expected:
        raise ValueError('exact membership mismatch')
    if 'FINAL.md' not in expected:
        raise ValueError('FINAL absent from manifest')
    return len(expected)

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', required=True)
    p.add_argument('--final-sha256', required=True)
    p.add_argument('--manifest-sha256', required=True)
    p.add_argument('--report-sha256', required=True)
    a = p.parse_args()
    try:
        n = verify(a.root, a.final_sha256, a.manifest_sha256, a.report_sha256)
    except (OSError, ValueError, KeyError, TypeError) as e:
        print('INTEGRITY FAILURE: ' + str(e), file=sys.stderr)
        raise SystemExit(1)
    print('INTEGRITY OK: %d exact selected files; no mathematical gate implied.' % n)
