#!/usr/bin/env python3
"""Read-only exact review inventory verification; assigns no mathematical gate."""
import argparse
import hashlib
import json
import os
import stat
from pathlib import Path, PurePosixPath


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory(root):
    base = root / 'packet'
    if base.is_symlink() or not base.is_dir():
        raise ValueError('packet must be a real directory')
    files, dirs = {}, ['packet']
    for current, names, leaves in os.walk(base, followlinks=False):
        for name in sorted(names):
            p = Path(current) / name
            if p.is_symlink():
                raise ValueError('symlink directory: ' + str(p))
            dirs.append(p.relative_to(root).as_posix())
        for name in sorted(leaves):
            p = Path(current) / name
            st = p.lstat()
            if not stat.S_ISREG(st.st_mode):
                raise ValueError('nonregular file: ' + str(p))
            rel = p.relative_to(root).as_posix()
            files[rel] = {'bytes': st.st_size, 'mode': oct(stat.S_IMODE(st.st_mode)), 'sha256': digest(p)}
    return files, sorted(dirs)


def verify(root, final_hash, manifest_hash, report_hash):
    for rel, expected in [('packet/FINAL.md', final_hash), ('MANIFEST.json', manifest_hash), ('REPORT.md', report_hash)]:
        if len(expected) != 64 or any(c not in '0123456789abcdef' for c in expected):
            raise ValueError('explicit lowercase SHA256 anchor required')
        p = root / rel
        if p.is_symlink() or not p.is_file() or digest(p) != expected:
            raise ValueError('detached anchor mismatch: ' + rel)
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    if manifest['format'] != 'r162m-contribution-r1-exact-v1' or manifest['scope'] != 'packet/':
        raise ValueError('wrong manifest format or scope')
    expected = {}
    for row in manifest['files']:
        rel = row['path']
        path = PurePosixPath(rel)
        if path.is_absolute() or '..' in path.parts or path.parts[0] != 'packet' or str(path) != rel or rel in expected:
            raise ValueError('invalid/duplicate manifest path')
        expected[rel] = {k: row[k] for k in ('bytes', 'mode', 'sha256')}
    actual, dirs = inventory(root)
    if actual != expected:
        raise ValueError('packet files, sizes, modes, or hashes differ')
    if dirs != manifest['directories']:
        raise ValueError('packet directory inventory differs')
    return {'artifact_check': 'matched', 'files': len(actual), 'mathematical_gate': 'not assigned'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True)
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--report-sha256', required=True)
    args = parser.parse_args()
    try:
        result = verify(Path(args.root), args.final_sha256, args.manifest_sha256, args.report_sha256)
    except (ValueError, KeyError, OSError, json.JSONDecodeError) as exc:
        parser.exit(1, str(exc) + '\n')
    print(json.dumps(result, sort_keys=True))
