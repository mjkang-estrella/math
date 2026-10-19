#!/usr/bin/env python3
"""Read-only exact inventory verification. Original code: MIT.
An external detached manifest digest is REQUIRED. This checks bytes, not mathematics.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

HEX = re.compile(r'[0-9a-f]{64}\Z')

def require(condition, message):
    if not condition:
        raise ValueError(message)

def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON key: ' + key)
        result[key] = value
    return result

def safe_path(value):
    require(isinstance(value, str) and value != '', 'empty/non-string path')
    require('\\' not in value and '\x00' not in value and ':' not in value, 'unsafe path')
    parts = value.split('/')
    require(all(p not in ('', '.', '..') for p in parts), 'unsafe path components')
    require(not PurePosixPath(value).is_absolute(), 'absolute inventory path')
    return value

def check(root, anchor):
    require(HEX.fullmatch(anchor) is not None, 'anchor must be lowercase SHA256')
    require(not root.is_symlink() and root.is_dir(), 'root must be a real directory')
    manifest_path = root / 'manifest.json'
    require(not manifest_path.is_symlink() and manifest_path.is_file(), 'manifest must be a regular file')
    raw = manifest_path.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == anchor, 'external manifest digest mismatch')
    data = json.loads(raw, object_pairs_hook=unique_object)
    require(isinstance(data, dict) and set(data) == {'schema', 'claim', 'files', 'directories'}, 'invalid manifest keys')
    require(data['schema'] == 'exact-inventory-v1', 'unknown schema')
    require(data['claim'] == 'evidence integrity only; no mathematical certification', 'invalid claim')
    require(isinstance(data['files'], list) and isinstance(data['directories'], list), 'invalid inventory arrays')
    files = {}
    order = []
    for item in data['files']:
        require(isinstance(item, dict) and set(item) == {'path', 'bytes', 'sha256'}, 'invalid file record')
        name = safe_path(item['path'])
        require(name != 'manifest.json' and name not in files, 'duplicate/reserved file path')
        require(type(item['bytes']) is int and item['bytes'] >= 0, 'invalid file length')
        require(isinstance(item['sha256'], str) and HEX.fullmatch(item['sha256']) is not None, 'invalid file digest')
        files[name] = item
        order.append(name)
    require(order == sorted(order), 'unsorted file inventory')
    dirs = [safe_path(p) for p in data['directories']]
    require(dirs == sorted(set(dirs)), 'duplicate/unsorted directory inventory')
    require(not set(dirs).intersection(files), 'file/directory collision')
    actual_files, actual_dirs = set(), set()
    for current, dirnames, filenames in os.walk(root, followlinks=False):
        for name in dirnames + filenames:
            path = Path(current) / name
            relative = path.relative_to(root).as_posix()
            mode = path.lstat().st_mode
            require(not stat.S_ISLNK(mode), 'symlink: ' + relative)
            if stat.S_ISDIR(mode):
                actual_dirs.add(relative)
            elif stat.S_ISREG(mode):
                actual_files.add(relative)
            else:
                raise ValueError('special file: ' + relative)
    require(actual_dirs == set(dirs), 'directory inventory mismatch')
    require(actual_files == set(files) | {'manifest.json'}, 'file inventory mismatch')
    for name, item in files.items():
        payload = (root / name).read_bytes()
        require(len(payload) == item['bytes'], 'byte length mismatch: ' + name)
        require(hashlib.sha256(payload).hexdigest() == item['sha256'], 'SHA256 mismatch: ' + name)
    freeze = json.loads((root / 'scope-freeze.json').read_bytes(), object_pairs_hook=unique_object)
    target = safe_path(freeze['path'])
    require(target in files and freeze['sha256'] == files[target]['sha256'] and freeze['bytes'] == files[target]['bytes'], 'frozen scope receipt mismatch')
    return {'status': 'VERIFIED_INVENTORY_ONLY', 'files': len(files), 'directories': len(dirs), 'manifest_sha256': anchor, 'mathematics': 'not certified'}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest-sha256', required=True, help='external detached digest; never inferred from local files')
    parser.add_argument('--root', type=Path, default=Path(__file__).absolute().parent.parent)
    args = parser.parse_args()
    try:
        print(json.dumps(check(Path(os.path.abspath(args.root)), args.manifest_sha256), sort_keys=True))
    except (OSError, ValueError, TypeError, KeyError, UnicodeError) as error:
        print('INVENTORY_REJECTED: ' + str(error), file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
