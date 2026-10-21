"""Read-only artifact verifier. Explicit detached anchors are mandatory.
No imports of local project code, writes, network, scans, or mathematical gates.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re


def check_file(path, size, expected):
    if path.is_symlink() or not path.is_file():
        raise ValueError('missing or symlink file: ' + str(path))
    data = path.read_bytes()
    if size is not None and len(data) != size:
        raise ValueError('byte length mismatch: ' + str(path))
    if hashlib.sha256(data).hexdigest() != expected:
        raise ValueError('SHA256 mismatch: ' + str(path))
    return data


def verify(root, final_sha, manifest_sha, report_sha):
    for value in (final_sha, manifest_sha, report_sha):
        if not re.fullmatch('[0-9a-f]{64}', value):
            raise ValueError('provide three explicit lowercase SHA256 anchors')
    root = root.resolve(strict=True)
    check_file(root / 'FINAL.md', None, final_sha)
    raw = check_file(root / 'MANIFEST.json', None, manifest_sha)
    check_file(root / 'REPORT.md', None, report_sha)
    manifest = json.loads(raw)
    if manifest['format'] != 'r167-selected-local-packet-v1':
        raise ValueError('unexpected manifest format')
    seen = set()
    for item in manifest['files']:
        name = item['path']
        pp = PurePosixPath(name)
        if pp.is_absolute() or '..' in pp.parts or '.' in pp.parts or str(pp) != name:
            raise ValueError('noncanonical relative path')
        if name in seen or name in ('MANIFEST.json', 'REPORT.md', 'ANCHORS.json'):
            raise ValueError('duplicate or detached path in manifest')
        seen.add(name)
        p = root.joinpath(*pp.parts)
        if not p.resolve(strict=True).is_relative_to(root):
            raise ValueError('path escapes explicit packet root')
        if any(root.joinpath(*pp.parts[:i]).is_symlink() for i in range(1, len(pp.parts) + 1)):
            raise ValueError('symlink in selected path')
        check_file(p, item['bytes'], item['sha256'])
    if 'FINAL.md' not in seen or 'verify_packet.py' not in seen:
        raise ValueError('required selected artifacts absent')
    return len(seen)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', required=True)
    p.add_argument('--final-sha256', required=True)
    p.add_argument('--manifest-sha256', required=True)
    p.add_argument('--report-sha256', required=True)
    a = p.parse_args()
    try:
        n = verify(Path(a.root), a.final_sha256, a.manifest_sha256, a.report_sha256)
    except (ValueError, OSError, KeyError, TypeError) as exc:
        print('ARTIFACT MISMATCH: ' + str(exc))
        return 1
    print('Artifact identities verified for ' + str(n) + ' selected files and three detached anchors; no mathematical verdict.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
