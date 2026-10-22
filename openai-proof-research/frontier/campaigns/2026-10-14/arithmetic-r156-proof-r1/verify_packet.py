#!/usr/bin/env python3
"""Read-only artifact verification; hashes must be supplied out of band."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat


def digest(data):
    return hashlib.sha256(data).hexdigest()


def safe_path(root, name):
    p = PurePosixPath(name)
    assert not p.is_absolute() and str(p) == name and name and '..' not in p.parts, 'unsafe path'
    q = root
    for part in p.parts:
        q = q / part
        assert not q.is_symlink(), 'symlink: ' + name
    return q


def verify(root, final_sha, manifest_sha, report_sha, project=None):
    expected = {'FINAL.md': final_sha, 'MANIFEST.json': manifest_sha, 'REPORT.md': report_sha}
    for name, sha in expected.items():
        assert len(sha) == 64 and all(c in '0123456789abcdef' for c in sha), 'invalid explicit anchor'
        assert digest(safe_path(root, name).read_bytes()) == sha, 'anchor mismatch: ' + name
    anchors = ''.join(sha + '  ' + name + '\n' for name, sha in expected.items())
    assert safe_path(root, 'ANCHORS.sha256').read_text() == anchors, 'detached-anchor mismatch'
    m = json.loads((root / 'MANIFEST.json').read_bytes())
    assert m['format'] == 'r156-review-exact-packet-v1', 'wrong format'
    exterior = {'MANIFEST.json', 'REPORT.md', 'ANCHORS.sha256'}
    assert set(m['exterior']) == exterior and len(m['exterior']) == 3
    selected = set()
    for item in m['files']:
        name = item['path']
        assert name not in selected and name not in exterior, 'duplicate/exterior payload'
        selected.add(name)
        q = safe_path(root, name)
        b = q.read_bytes()
        assert len(b) == item['bytes'] and digest(b) == item['sha256'], 'payload mismatch: ' + name
        assert stat.S_IMODE(q.stat().st_mode) == item['mode'], 'mode mismatch: ' + name
    actual = set()
    for base, dirs, files in os.walk(root, followlinks=False):
        for name in dirs + files:
            q = Path(base) / name
            assert not q.is_symlink(), 'symlink in packet'
        for name in files:
            actual.add((Path(base) / name).relative_to(root).as_posix())
    assert actual == selected | exterior, 'exact selected-set mismatch'
    assert 'FINAL.md' in selected, 'FINAL not in payload'
    checked = 0
    if project is not None:
        for item in json.loads((root / 'private/original-checks.json').read_bytes()):
            q = safe_path(project, item['path'])
            with q.open('rb') as f:
                f.seek(item.get('start', 0))
                b = f.read(item['bytes']) if 'start' in item else f.read()
            assert len(b) == item['bytes'] and digest(b) == item['sha256'], 'original bytes changed: ' + item['path']
            if 'mode' in item:
                assert stat.S_IMODE(q.stat().st_mode) == item['mode'], 'original mode changed'
            checked += 1
    return {'artifact_consistent': True, 'selected_files': len(selected), 'explicit_original_checks': checked,
            'mathematical_gate': False}


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('packet', type=Path)
    ap.add_argument('--final-sha', required=True)
    ap.add_argument('--manifest-sha', required=True)
    ap.add_argument('--report-sha', required=True)
    ap.add_argument('--project', type=Path)
    args = ap.parse_args()
    try:
        result = verify(args.packet, args.final_sha, args.manifest_sha, args.report_sha, args.project)
    except (AssertionError, OSError, ValueError, KeyError) as exc:
        print(json.dumps({'artifact_consistent': False, 'error': str(exc), 'mathematical_gate': False}))
        raise SystemExit(1)
    print(json.dumps(result, sort_keys=True))
