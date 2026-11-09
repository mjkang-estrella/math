#!/usr/bin/env python3
"""Read-only packet verification. Explicit detached anchors are mandatory.

Example: python verify.py --final SHA256:BYTES:FULL_MODE \
 --manifest SHA256:BYTES:FULL_MODE --report SHA256:BYTES:FULL_MODE
Add --check-author to hash only the 61 exact authorized original files.
No author verifier, completed bindings, network, writes, or ancestor traversal.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import os
import stat

DETACHED = ('FINAL.md', 'MANIFEST.json', 'REPORT.md')
PROJECT = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
AUTHOR = 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cb/'

def require(test, message):
    if not test:
        raise ValueError(message)

def safe(name, directory=False):
    require(isinstance(name, str) and name != '', 'empty/nonstring name')
    if directory and name == '.':
        return
    p = PurePosixPath(name)
    require(not p.is_absolute() and str(p) == name, 'noncanonical path: '+name)
    require(all(x not in ('', '.', '..') for x in p.parts), 'unsafe path: '+name)
    require('\\' not in name and all(ord(c) >= 32 for c in name), 'unsafe path characters')

def digest(data):
    return hashlib.sha256(data).hexdigest()

def anchor(data, mode):
    return {'sha256': digest(data), 'bytes': len(data), 'mode': mode}

def snapshot(root):
    """Read only this root; reject links/special files before descent or reads."""
    root = Path(root)
    require(stat.S_ISDIR(root.lstat().st_mode), 'root is not a real directory')
    files, directories = {}, {'.': root.lstat().st_mode}
    def walk(directory):
        for entry in sorted(os.scandir(directory), key=lambda e: e.name):
            path = Path(entry.path)
            rel = path.relative_to(root).as_posix()
            safe(rel)
            mode = entry.stat(follow_symlinks=False).st_mode
            if stat.S_ISDIR(mode):
                directories[rel] = mode
                walk(path)
            else:
                require(stat.S_ISREG(mode), 'link/special file rejected: '+rel)
                files[rel] = (path.read_bytes(), mode)
    walk(root)
    return files, directories

def verify_snapshot(files, directories, anchors):
    """Same validation logic for preflight, tiny controls, and final disk state."""
    require(set(anchors) == set(DETACHED), 'all three explicit anchors required')
    for name in files:
        safe(name)
    for name, mode in directories.items():
        safe(name, directory=True)
        require(stat.S_ISDIR(mode), 'not a directory mode: '+name)
    for name in DETACHED:
        require(name in files, 'missing detached object: '+name)
        data, mode = files[name]
        require(anchor(data, mode) == anchors[name], 'detached anchor mismatch: '+name)
    manifest = json.loads(files['MANIFEST.json'][0])
    require(manifest['schema'] == 'R162CB-proof-r1-seal-v1', 'wrong schema')
    rows, dirs = manifest['files'], manifest['directories']
    names = [r['path'] for r in rows]
    dnames = [r['path'] for r in dirs]
    require(names == sorted(set(names)), 'file records not sorted unique')
    require(dnames == sorted(set(dnames)), 'directory records not sorted unique')
    require('FINAL.md' in names and 'MANIFEST.json' not in names and 'REPORT.md' not in names,
            'wrong detached membership')
    require(set(files) == set(names) | {'MANIFEST.json', 'REPORT.md'}, 'file membership mismatch')
    require(set(directories) == set(dnames), 'directory membership mismatch')
    for r in rows:
        name = r['path']; safe(name)
        require(set(r) == {'path','sha256','bytes','mode'}, 'invalid file record')
        require(stat.S_ISREG(r['mode']), 'nonregular file record')
        data, mode = files[name]
        require(anchor(data, mode) == {k:r[k] for k in ('sha256','bytes','mode')},
                'file bytes/mode mismatch: '+name)
    for r in dirs:
        name = r['path']; safe(name, directory=True)
        require(set(r) == {'path','mode'}, 'invalid directory record')
        require(directories[name] == r['mode'], 'full directory mode mismatch: '+name)
    require(manifest['detached_outside_payload'] == ['MANIFEST.json','REPORT.md'],
            'incorrect outside-payload declaration')
    return {'payload_files':len(rows),'total_files':len(files),'directories':len(dirs)}

def check_author(root):
    rows = json.loads((root/'private/author-before.json').read_bytes())
    require(len(rows) == 61, 'expected 61 exact author records')
    names = [r['path'] for r in rows]
    require(len(set(names)) == 61, 'duplicate author binding')
    for r in rows:
        name = r['path']; safe(name)
        require(name.startswith(AUTHOR), 'author path outside exact authorized root')
        p = PROJECT/name
        mode = p.lstat().st_mode
        require(stat.S_ISREG(mode), 'author file not regular')
        # Raw-byte integrity only, including semantic-false records.
        require(anchor(p.read_bytes(), mode) == {k:r[k] for k in ('sha256','bytes','mode')},
                'author integrity mismatch: '+name)
    return 61

def parse_anchor(value):
    sha, size, mode = value.split(':')
    require(len(sha) == 64 and all(c in '0123456789abcdef' for c in sha), 'invalid SHA256')
    size, mode = int(size), int(mode)
    require(size >= 0 and stat.S_ISREG(mode), 'invalid size/full regular-file mode')
    return {'sha256':sha,'bytes':size,'mode':mode}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('final','manifest','report'):
        parser.add_argument('--'+name, required=True, type=parse_anchor)
    parser.add_argument('--check-author', action='store_true')
    args = parser.parse_args()
    root = Path(__file__).absolute().parent
    anchors = {'FINAL.md':args.final,'MANIFEST.json':args.manifest,'REPORT.md':args.report}
    result = verify_snapshot(*snapshot(root), anchors)
    if args.check_author:
        result['author_files_unchanged'] = check_author(root)
    print(json.dumps({'artifact_verification':'MATCH','mathematical_gate':False,**result},sort_keys=True))

if __name__ == '__main__':
    main()
