#!/usr/bin/env python3
"""Read-only exact packet verifier. All three detached anchors are required.

No author input is opened, no network is used, and no file is written. A success
is an integrity result only; it assigns no mathematical grade.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def unique_object(pairs):
    out = {}
    for key, value in pairs:
        require(key not in out, 'duplicate JSON key: ' + key)
        out[key] = value
    return out


def safe_path(value, root_allowed=False):
    require(isinstance(value, str), 'path must be text')
    if root_allowed and value == '.':
        return value
    require(value and '\\' not in value and '\x00' not in value,
            'unsafe path characters')
    p = PurePosixPath(value)
    require(not p.is_absolute() and p.as_posix() == value,
            'noncanonical path: ' + value)
    require(all(x not in ('', '.', '..') for x in value.split('/')),
            'unsafe path component: ' + value)
    return value


def inventory(root):
    files, directories = {}, {}
    require(not root.is_symlink(), 'root must not be a symlink')
    def visit(path, relative):
        st = path.lstat()
        require(stat.S_ISDIR(st.st_mode), 'not a directory: ' + relative)
        directories[relative] = st.st_mode
        for entry in sorted(os.scandir(path), key=lambda x: x.name):
            rel = entry.name if relative == '.' else relative + '/' + entry.name
            safe_path(rel)
            st = entry.stat(follow_symlinks=False)
            if stat.S_ISDIR(st.st_mode):
                visit(Path(entry.path), rel)
            else:
                require(stat.S_ISREG(st.st_mode), 'nonregular member: ' + rel)
                require(st.st_nlink == 1, 'hardlinked member: ' + rel)
                data = Path(entry.path).read_bytes()
                files[rel] = dict(path=rel, bytes=len(data), mode=st.st_mode,
                                  sha256=sha(data))
    visit(root, '.')
    return files, directories


def verify(root, final_sha, manifest_sha, report_sha):
    root = Path(root)
    for anchor in (final_sha, manifest_sha, report_sha):
        require(isinstance(anchor, str) and re.fullmatch('[0-9a-f]{64}', anchor),
                'each explicit detached anchor must be lowercase SHA256')
    files, directories = inventory(root)
    for name, expected in [('FINAL.md', final_sha), ('MANIFEST.json', manifest_sha),
                           ('REPORT.md', report_sha)]:
        require(name in files, 'missing anchor member: ' + name)
        require(files[name]['sha256'] == expected, 'detached anchor mismatch: ' + name)
    manifest = json.loads((root / 'MANIFEST.json').read_bytes(), object_pairs_hook=unique_object)
    require(set(manifest) == {'format', 'files', 'directories', 'outside_manifest'},
            'unexpected manifest schema')
    require(manifest['format'] == 'r162bm-contribution-r1-exact-v1', 'wrong format')
    records = manifest['files']
    require(isinstance(records, list), 'files must be a list')
    names = []
    for record in records:
        require(isinstance(record, dict) and set(record) == {'path', 'bytes', 'mode', 'sha256'},
                'unexpected file record')
        name = safe_path(record['path'])
        names.append(name)
        require(name not in ('MANIFEST.json', 'REPORT.md'), 'outside file in payload')
        require(type(record['bytes']) is int and record['bytes'] >= 0, 'invalid byte length')
        require(type(record['mode']) is int and stat.S_ISREG(record['mode']), 'invalid full file mode')
        require(isinstance(record['sha256'], str) and re.fullmatch('[0-9a-f]{64}', record['sha256']),
                'invalid file hash')
        require(name in files and files[name] == record, 'file record mismatch: ' + name)
    require(names == sorted(set(names)), 'file records must be unique and sorted')
    require(set(files) == set(names) | {'MANIFEST.json', 'REPORT.md'}, 'file membership mismatch')
    require('FINAL.md' in names, 'FINAL missing from payload')
    drecs = manifest['directories']
    require(isinstance(drecs, list), 'directories must be a list')
    dnames = []
    for record in drecs:
        require(isinstance(record, dict) and set(record) == {'path', 'mode'}, 'unexpected directory record')
        name = safe_path(record['path'], root_allowed=True)
        dnames.append(name)
        require(type(record['mode']) is int and stat.S_ISDIR(record['mode']), 'invalid full directory mode')
        require(directories.get(name) == record['mode'], 'directory mode mismatch: ' + name)
    require(dnames == sorted(set(dnames)), 'directory records must be unique and sorted')
    require(set(directories) == set(dnames), 'directory membership mismatch')
    outside = manifest['outside_manifest']
    require(isinstance(outside, list) and [x.get('path') for x in outside] == ['MANIFEST.json', 'REPORT.md'],
            'outside members must be exact and sorted')
    for record in outside:
        require(set(record) == {'path', 'mode'}, 'unexpected outside record')
        require(type(record['mode']) is int and files[record['path']]['mode'] == record['mode'],
                'outside full mode mismatch')
    return dict(integrity='MATCH', files=len(files), payload_files=len(records),
                directories=len(directories), mathematical_gate=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True)
    parser.add_argument('--final-sha', required=True)
    parser.add_argument('--manifest-sha', required=True)
    parser.add_argument('--report-sha', required=True)
    args = parser.parse_args()
    try:
        result = verify(args.root, args.final_sha, args.manifest_sha, args.report_sha)
    except (ValueError, OSError, TypeError, KeyError) as exc:
        parser.exit(1, 'INTEGRITY MISMATCH: ' + str(exc) + '\n')
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
