#!/usr/bin/env python3
"""Read-only byte/mode verifier. Supply all three detached anchors explicitly."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

EXTERIOR = {'MANIFEST.json', 'REPORT.md', 'ANCHORS.json'}
CONTROL = 'private/controls'

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def inventory(root):
    result = {}
    for base, directories, files in os.walk(root, followlinks=False):
        base = Path(base)
        keep = []
        for name in directories:
            p = base / name
            rel = p.relative_to(root).as_posix()
            if p.is_symlink():
                raise ValueError('symlink directory: ' + rel)
            if rel != CONTROL:
                keep.append(name)
        directories[:] = sorted(keep)
        for name in sorted(files):
            p = base / name
            rel = p.relative_to(root).as_posix()
            if p.is_symlink() or not stat.S_ISREG(p.stat().st_mode):
                raise ValueError('nonregular file: ' + rel)
            if rel not in EXTERIOR:
                result[rel] = p
    return result

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True)
    parser.add_argument('--final-sha', required=True)
    parser.add_argument('--manifest-sha', required=True)
    parser.add_argument('--report-sha', required=True)
    args = parser.parse_args()
    root = Path(args.root).absolute()
    if root.is_symlink() or not root.is_dir():
        raise ValueError('root must be a real directory')
    for name, expected in [('FINAL.md', args.final_sha), ('MANIFEST.json', args.manifest_sha), ('REPORT.md', args.report_sha)]:
        if not re.fullmatch('[0-9a-f]{64}', expected):
            raise ValueError('invalid explicit anchor for ' + name)
        p = root / name
        if p.is_symlink() or not p.is_file() or digest(p) != expected:
            raise ValueError('detached anchor mismatch: ' + name)
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    if manifest.get('excluded_root_files') != sorted(EXTERIOR) or manifest.get('excluded_subtrees') != [CONTROL + '/']:
        raise ValueError('unexpected selection policy')
    actual = inventory(root)
    selected = {}
    for entry in manifest['files']:
        rel = entry['path']
        path = PurePosixPath(rel)
        if (path.is_absolute() or '..' in path.parts or rel != path.as_posix()
                or rel in EXTERIOR or rel == CONTROL or rel.startswith(CONTROL + '/') or rel in selected):
            raise ValueError('invalid or duplicate selected path: ' + rel)
        selected[rel] = entry
    if set(actual) != set(selected):
        raise ValueError('selection differs: missing=' + repr(sorted(set(selected)-set(actual))) + '; extra=' + repr(sorted(set(actual)-set(selected))))
    total = 0
    for rel, entry in selected.items():
        p = actual[rel]
        info = p.stat()
        if (info.st_size != entry['bytes'] or digest(p) != entry['sha256']
                or stat.S_IMODE(info.st_mode) != entry['mode']):
            raise ValueError('payload bytes or mode differ: ' + rel)
        total += info.st_size
    if manifest.get('file_count') != len(selected) or manifest.get('total_bytes') != total:
        raise ValueError('manifest totals differ')
    print('Artifact bytes, modes and exact selection verified: %d files, %d bytes. No mathematical gate.' % (len(selected), total))

if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError) as exc:
        print('Verification failed: ' + str(exc), file=sys.stderr)
        sys.exit(1)
