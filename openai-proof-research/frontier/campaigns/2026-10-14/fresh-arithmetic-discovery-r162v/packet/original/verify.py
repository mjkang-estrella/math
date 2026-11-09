#!/usr/bin/env python3
# Read-only exact-packet verifier. All three detached anchors are REQUIRED.
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import sys


def digest(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def anchored(path, expected):
    require(re.fullmatch(r'[0-9a-f]{64}', expected) is not None, 'invalid explicit anchor')
    require(not path.is_symlink() and path.is_file(), 'anchor path is not a regular file')
    data = path.read_bytes()
    require(digest(data) == expected, 'detached anchor mismatch: ' + path.name)
    return data


def verify(root, final_hash, manifest_hash, report_hash):
    require(not root.is_symlink() and root.is_dir(), 'invalid root')
    anchored(root / 'FINAL.md', final_hash)
    raw = anchored(root / 'MANIFEST.json', manifest_hash)
    anchored(root / 'REPORT.md', report_hash)
    manifest = json.loads(raw)
    require(manifest.get('format') == 'r162v-exact-packet-v1', 'unknown manifest format')
    require(manifest.get('packet') == 'packet', 'unexpected packet root')
    require(manifest.get('final_sha256') == final_hash, 'manifest/final mismatch')
    packet = root / 'packet'
    require(packet.is_dir() and not packet.is_symlink(), 'invalid packet directory')
    files, directories = set(), set()
    for base, dirs, names in os.walk(packet, topdown=True, followlinks=False):
        for name in dirs:
            path = Path(base) / name
            require(not path.is_symlink(), 'symlink directory forbidden')
            directories.add(path.relative_to(packet).as_posix())
        for name in names:
            path = Path(base) / name
            require(not path.is_symlink() and path.is_file(), 'nonregular packet object')
            files.add(path.relative_to(packet).as_posix())
    expected, byte_count = set(), 0
    for item in manifest['files']:
        name = item['path']
        posix = PurePosixPath(name)
        require(name and not posix.is_absolute() and '..' not in posix.parts
                and str(posix) == name and name not in expected, 'unsafe or duplicate path')
        expected.add(name)
        require(name in files, 'missing packet file: ' + name)
        data = (packet / name).read_bytes()
        require(len(data) == item['bytes'], 'packet size mismatch: ' + name)
        require(digest(data) == item['sha256'], 'packet hash mismatch: ' + name)
        byte_count += len(data)
    require(files == expected, 'unexpected packet file')
    require(directories == set(manifest['directories'])
            and len(directories) == len(manifest['directories']), 'packet directory mismatch')
    return {'ok': True, 'files': len(files), 'bytes': byte_count,
            'meaning': 'artifact integrity only; no mathematical gate'}


def main():
    parser = argparse.ArgumentParser(description='Read-only verifier with explicit detached anchors')
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--report-sha256', required=True)
    args = parser.parse_args()
    try:
        result = verify(args.root, args.final_sha256, args.manifest_sha256, args.report_sha256)
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(json.dumps({'ok': False, 'error': str(error)}))
        return 1
    print(json.dumps(result))
    return 0


if __name__ == '__main__':
    sys.exit(main())
