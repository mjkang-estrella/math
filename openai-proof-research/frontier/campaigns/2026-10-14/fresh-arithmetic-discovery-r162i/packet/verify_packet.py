#!/usr/bin/env python3
"""Read-only byte verifier; explicit detached anchors are mandatory. No math gate."""
import argparse
import hashlib
import json
from pathlib import Path
import stat
import sys

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def verify(root, anchors):
    root = Path(root)
    for rel, expected in zip(('packet/FINAL.md', 'MANIFEST.json', 'REPORT.md'), anchors):
        if len(expected) != 64 or any(c not in '0123456789abcdef' for c in expected):
            raise ValueError('Invalid explicit anchor: ' + rel)
        q = root / rel
        if q.is_symlink() or not q.is_file() or digest(q) != expected:
            raise ValueError('Detached anchor mismatch: ' + rel)
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    packet = root / 'packet'
    actual = {}
    for q in packet.rglob('*'):
        if q.is_symlink():
            raise ValueError('Symlink in packet: ' + str(q))
        if q.is_file():
            rel = q.relative_to(packet).as_posix()
            actual[rel] = {'path': rel, 'bytes': q.stat().st_size,
                           'sha256': digest(q), 'mode': stat.S_IMODE(q.stat().st_mode)}
    expected = {}
    for entry in manifest['files']:
        rel = entry['path']
        if Path(rel).is_absolute() or '..' in Path(rel).parts or rel in expected:
            raise ValueError('Invalid or duplicate manifest path')
        expected[rel] = entry
    if actual != expected:
        missing = sorted(set(expected) - set(actual))
        extra = sorted(set(actual) - set(expected))
        changed = sorted(k for k in set(expected) & set(actual) if expected[k] != actual[k])
        raise ValueError(json.dumps({'missing': missing, 'extra': extra, 'changed': changed}))
    return {'artifact_match': True, 'files': len(actual),
            'bytes': sum(x['bytes'] for x in actual.values()), 'mathematical_gate': False}

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('root')
    ap.add_argument('--final-sha', required=True)
    ap.add_argument('--manifest-sha', required=True)
    ap.add_argument('--report-sha', required=True)
    a = ap.parse_args()
    try:
        print(json.dumps(verify(a.root, (a.final_sha, a.manifest_sha, a.report_sha)), sort_keys=True))
    except (ValueError, OSError, KeyError, json.JSONDecodeError) as exc:
        print('ARTIFACT MISMATCH: ' + str(exc), file=sys.stderr)
        sys.exit(1)
