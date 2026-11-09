#!/usr/bin/env python3
"""Read-only exact-packet verifier. Supply all three detached SHA256 anchors."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import stat


def digest(data):
    return hashlib.sha256(data).hexdigest()


def safe(name):
    p = PurePosixPath(name)
    return (isinstance(name, str) and name != '' and not p.is_absolute()
            and str(p) == name and all(x not in ('', '.', '..') for x in p.parts)
            and '\\' not in name and '\x00' not in name)


def files(root):
    """Walk only the supplied packet; reject links without descending into them."""
    found = []
    pending = [root]
    while pending:
        directory = pending.pop()
        assert stat.S_ISDIR(directory.lstat().st_mode), 'Non-directory or link'
        for p in directory.iterdir():
            mode = p.lstat().st_mode
            if stat.S_ISDIR(mode):
                pending.append(p)
            else:
                assert stat.S_ISREG(mode), 'Link or special file'
                found.append(p.relative_to(root).as_posix())
    return sorted(found)


def entries_for(root, names):
    assert names == sorted(set(names)) and all(safe(n) for n in names)
    out = []
    for name in names:
        p = root / name
        mode = p.lstat().st_mode
        assert stat.S_ISREG(mode)
        data = p.read_bytes()
        out.append({'path': name, 'bytes': len(data), 'sha256': digest(data), 'mode': mode})
    return out


def validate_payload(root, entries, detached_present):
    names = [e['path'] for e in entries]
    assert names == sorted(set(names)) and all(safe(n) for n in names), 'Unsafe or unsorted membership'
    assert 'FINAL.md' in names and 'MANIFEST.json' not in names and 'REPORT.md' not in names
    expected = sorted(names + (['MANIFEST.json', 'REPORT.md'] if detached_present else []))
    assert files(root) == expected, 'Exact membership mismatch'
    assert entries_for(root, names) == entries, 'Payload bytes or full modes differ'
    if detached_present:
        for name in ['MANIFEST.json', 'REPORT.md']:
            assert (root / name).lstat().st_mode == 0o100644, 'Detached full mode differs'
    return len(entries)


def verify(root, final_anchor, manifest_anchor, report_anchor):
    for name, anchor in [('FINAL.md', final_anchor), ('MANIFEST.json', manifest_anchor), ('REPORT.md', report_anchor)]:
        assert re.fullmatch('[0-9a-f]{64}', anchor), 'Explicit SHA256 anchor required'
        p = root / name
        assert stat.S_ISREG(p.lstat().st_mode), 'Detached link or special file'
        assert digest(p.read_bytes()) == anchor, 'Detached anchor mismatch: ' + name
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    assert manifest['format'] == 'r162cp-independent-review-v1'
    assert manifest['detached_outside_payload'] == ['MANIFEST.json', 'REPORT.md']
    assert manifest['final'] == 'FINAL.md'
    return validate_payload(root, manifest['files'], True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', type=Path, required=True)
    p.add_argument('--final-sha256', required=True)
    p.add_argument('--manifest-sha256', required=True)
    p.add_argument('--report-sha256', required=True)
    a = p.parse_args()
    count = verify(a.root, a.final_sha256, a.manifest_sha256, a.report_sha256)
    print('PASS: exact membership, bytes, full modes and all detached anchors;', count, 'payload files')
