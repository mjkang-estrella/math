"""Read-only exact-selection artifact verifier. It does not assess mathematics.

Pass all three detached SHA256 anchors literally. No source navigation,
network access, subprocess, writes, chmod, or inherited-manifest selection.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import sys


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def inventory(packet):
    entries = []
    if packet.is_symlink() or not packet.is_dir():
        raise ValueError('packet must be an ordinary directory')
    for directory, dirs, files in os.walk(packet, followlinks=False):
        dirs.sort()
        files.sort()
        for name in dirs + files:
            p = Path(directory) / name
            s = p.lstat()
            rel = p.relative_to(packet).as_posix()
            if stat.S_ISLNK(s.st_mode):
                raise ValueError('symlink in packet: ' + rel)
            if stat.S_ISDIR(s.st_mode):
                e = {'path': rel, 'type': 'directory', 'mode': stat.S_IMODE(s.st_mode)}
            elif stat.S_ISREG(s.st_mode):
                e = {'path': rel, 'type': 'file', 'mode': stat.S_IMODE(s.st_mode),
                     'bytes': s.st_size, 'sha256': digest(p)}
            else:
                raise ValueError('nonregular entry: ' + rel)
            entries.append(e)
    return sorted(entries, key=lambda e: e['path'])


def verify(root, anchors):
    for name in ('FINAL.md', 'MANIFEST.json', 'REPORT.md'):
        p = root / name
        if p.is_symlink() or not p.is_file():
            raise ValueError('detached artifact missing or symlink: ' + name)
        if digest(p) != anchors[name]:
            raise ValueError('detached anchor mismatch: ' + name)
    m = json.loads((root / 'MANIFEST.json').read_bytes())
    if m.get('format') != 'r227-exact-selected-packet-v1' or m.get('packet') != 'packet':
        raise ValueError('unsupported manifest shape')
    expected = m['entries']
    names = []
    for e in expected:
        path = e['path']
        p = PurePosixPath(path)
        if p.is_absolute() or '..' in p.parts or path != p.as_posix() or path in ('', '.'):
            raise ValueError('unsafe manifest path')
        names.append(path)
    if len(set(names)) != len(names):
        raise ValueError('duplicate selected path')
    packet = root / 'packet'
    actual = inventory(packet)
    if stat.S_IMODE(packet.stat().st_mode) != m['packet_mode']:
        raise ValueError('packet root mode mismatch')
    actual_names = [e['path'] for e in actual]
    if sorted(names) != actual_names:
        raise ValueError('exact selection mismatch')
    if sorted(expected, key=lambda e: e['path']) != actual:
        raise ValueError('selected bytes, hash, type, or mode mismatch')
    return {'ok': True, 'purpose': 'artifact integrity only; no mathematical grade',
            'files': sum(e['type'] == 'file' for e in actual),
            'directories': sum(e['type'] == 'directory' for e in actual)}


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--root', required=True)
    p.add_argument('--final-sha256', required=True)
    p.add_argument('--manifest-sha256', required=True)
    p.add_argument('--report-sha256', required=True)
    a = p.parse_args()
    anchors = {'FINAL.md': a.final_sha256, 'MANIFEST.json': a.manifest_sha256,
               'REPORT.md': a.report_sha256}
    try:
        for h in anchors.values():
            if len(h) != 64 or any(c not in '0123456789abcdef' for c in h):
                raise ValueError('invalid explicit SHA256 anchor')
        result = verify(Path(a.root), anchors)
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError) as e:
        print(json.dumps({'ok': False, 'error': str(e)}))
        return 1
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == '__main__':
    sys.exit(main())
