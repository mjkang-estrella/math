#!/usr/bin/env python3
"""Read-only exact-selection artifact check; never a mathematical gate."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat

def digest(data):
    return hashlib.sha256(data).hexdigest()

def verify(root, final_sha, manifest_sha, report_sha):
    root = Path(root).resolve(strict=True)
    anchors = {'FINAL.md': final_sha, 'MANIFEST.json': manifest_sha, 'REPORT.md': report_sha}
    for name, expected in anchors.items():
        assert re.fullmatch(r'[0-9a-f]{64}', expected), 'invalid explicit anchor'
        p = root / name
        assert not p.is_symlink() and p.is_file(), 'missing or linked anchor: ' + name
        assert digest(p.read_bytes()) == expected, 'detached anchor mismatch: ' + name
    carrier = json.loads((root / 'ANCHORS.json').read_text())
    assert carrier['sha256'] == anchors, 'carrier disagrees with explicit anchors'
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    assert manifest['format'] == 'structural195-contribution-exact-selection-v1'
    excluded = {'ANCHORS.json', 'MANIFEST.json', 'REPORT.md'}
    assert set(manifest['excluded_root_files']) == excluded
    assert manifest['excluded_subtrees'] == ['private/controls/']
    expected_paths = set()
    total = 0
    for item in manifest['files']:
        name = item['path']; q = PurePosixPath(name)
        assert name and not q.is_absolute() and name == q.as_posix()
        assert all(x not in ('', '.', '..') for x in q.parts)
        assert name not in excluded and q.parts[:2] != ('private', 'controls')
        assert name not in expected_paths, 'duplicate payload path'
        expected_paths.add(name)
        p = root / name
        for parent in [p, *p.parents]:
            if parent == root: break
            assert not parent.is_symlink(), 'symlink payload path'
        assert p.is_file(), 'missing payload: ' + name
        b = p.read_bytes()
        assert len(b) == item['bytes'], 'size mismatch: ' + name
        assert digest(b) == item['sha256'], 'hash mismatch: ' + name
        assert stat.S_IMODE(p.stat().st_mode) == item['mode'], 'mode mismatch: ' + name
        total += len(b)
    actual = set()
    for directory, dirs, files in os.walk(root, followlinks=False):
        base = Path(directory)
        if base == root / 'private':
            dirs[:] = [d for d in dirs if d != 'controls']
        for d in dirs:
            assert not (base / d).is_symlink(), 'linked directory'
        for name in files:
            p = base / name
            assert not p.is_symlink(), 'linked file'
            rel = p.relative_to(root).as_posix()
            if rel not in excluded: actual.add(rel)
    assert actual == expected_paths, 'exact-selection mismatch: ' + repr(sorted(actual ^ expected_paths))
    assert total == manifest['payload_bytes']
    return {'artifact_check': 'PASS', 'selected_files': len(expected_paths), 'payload_bytes': total,
            'mathematical_gate': False}

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', required=True)
    p.add_argument('--final-sha', required=True)
    p.add_argument('--manifest-sha', required=True)
    p.add_argument('--report-sha', required=True)
    a = p.parse_args()
    try:
        print(json.dumps(verify(a.root, a.final_sha, a.manifest_sha, a.report_sha), sort_keys=True))
    except (AssertionError, OSError, ValueError, KeyError, TypeError) as e:
        p.exit(1, 'Artifact verification FAILED: ' + str(e) + '\n')
if __name__ == '__main__':
    main()
