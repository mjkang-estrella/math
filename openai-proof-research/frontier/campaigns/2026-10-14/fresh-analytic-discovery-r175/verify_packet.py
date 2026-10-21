#!/usr/bin/env python3
"""Read-only byte verifier. Detached hashes MUST be supplied by the caller.

No mathematical validation is performed. No anchors are learned from ANCHORS.json.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath

OUTSIDE = {'FINAL.md', 'MANIFEST.json', 'REPORT.json', 'ANCHORS.json'}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def blob(path, expected):
    if path.is_symlink() or not path.is_file():
        raise ValueError('not a regular nonsymlink file: ' + str(path))
    data = path.read_bytes()
    if digest(data) != expected:
        raise ValueError('SHA256 mismatch: ' + str(path))
    return data


def packet(root, final_hash, manifest_hash, report_hash):
    if root.is_symlink() or not root.is_dir():
        raise ValueError('invalid packet root')
    blob(root / 'FINAL.md', final_hash)
    manifest = json.loads(blob(root / 'MANIFEST.json', manifest_hash))
    report = json.loads(blob(root / 'REPORT.json', report_hash))
    if report['final_sha256'] != final_hash or report['manifest_sha256'] != manifest_hash:
        raise ValueError('report cross-anchors disagree')
    expected_paths = set()
    for item in manifest['files']:
        name = item['path']
        rel = PurePosixPath(name)
        if rel.is_absolute() or '..' in rel.parts or str(rel) != name or name in OUTSIDE:
            raise ValueError('invalid manifest path: ' + name)
        if name in expected_paths:
            raise ValueError('duplicate manifest path: ' + name)
        expected_paths.add(name)
        current = root
        for part in rel.parts:
            current = current / part
            if current.is_symlink():
                raise ValueError('symlink: ' + name)
        data = blob(current, item['sha256'])
        if len(data) != item['bytes']:
            raise ValueError('length mismatch: ' + name)
    actual_paths = set()
    for current in root.rglob('*'):
        if current.is_symlink():
            raise ValueError('symlink in packet: ' + str(current))
        if current.is_file():
            name = current.relative_to(root).as_posix()
            if name not in OUTSIDE:
                actual_paths.add(name)
    if actual_paths != expected_paths:
        raise ValueError('exact packet coverage mismatch')
    return {'artifact_bytes_match': True, 'files': len(expected_paths),
            'mathematical_verdict': None}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path)
    parser.add_argument('--final-sha256')
    parser.add_argument('--manifest-sha256')
    parser.add_argument('--report-sha256')
    parser.add_argument('--blob', type=Path)
    parser.add_argument('--sha256')
    args = parser.parse_args()
    try:
        if args.blob is not None:
            if args.sha256 is None or args.root is not None:
                parser.error('blob mode requires --sha256 and no --root')
            blob(args.blob, args.sha256)
            print(json.dumps({'artifact_bytes_match': True, 'mathematical_verdict': None}))
        else:
            if not all((args.root, args.final_sha256, args.manifest_sha256, args.report_sha256)):
                parser.error('packet mode requires root and all three explicit detached hashes')
            print(json.dumps(packet(args.root, args.final_sha256, args.manifest_sha256,
                                    args.report_sha256)))
    except (ValueError, KeyError, OSError, TypeError) as exc:
        print(json.dumps({'artifact_bytes_match': False, 'error': str(exc),
                          'mathematical_verdict': None}))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
