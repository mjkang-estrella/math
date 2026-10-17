#!/usr/bin/env python3
"""Read-only external-anchor/exact-membership verifier. Identity, not mathematics."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat

SCHEMA = 'AGM063-independent-proof-review-r1'

def require(ok, reason):
    if not ok:
        raise ValueError(reason)

def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON key')
        result[key] = value
    return result

def safe(name):
    require(isinstance(name, str) and name and '\\' not in name, 'bad path')
    p = PurePosixPath(name)
    require(not p.is_absolute() and p.as_posix() == name and
            all(x not in ('.', '..', '') for x in p.parts), 'unsafe path')
    return name

def sha(data):
    return hashlib.sha256(data).hexdigest()

def verify(root, anchor):
    require(re.fullmatch('[0-9a-f]{64}', anchor) is not None, 'invalid external anchor')
    require(root.is_dir() and not root.is_symlink(), 'bad root')
    mp = root / 'review-manifest.json'
    require(mp.is_file() and not mp.is_symlink(), 'bad manifest')
    raw = mp.read_bytes()
    require(sha(raw) == anchor, 'external anchor mismatch')
    m = json.loads(raw, object_pairs_hook=unique)
    require(set(m) == {'schema', 'verdict', 'full_formalization', 'acceptance_claimed', 'files', 'directories'}, 'manifest fields')
    require(m['schema'] == SCHEMA and m['verdict'] == 'PASS_FULL_AGM063', 'schema/verdict')
    require(m['full_formalization'] is False and m['acceptance_claimed'] is False, 'scope flags')
    rows = {}
    for row in m['files']:
        require(set(row) == {'path', 'bytes', 'sha256'}, 'row fields')
        name = safe(row['path'])
        require(name not in rows and name != 'review-manifest.json', 'duplicate/self path')
        require(type(row['bytes']) is int and row['bytes'] >= 0, 'bad byte count')
        require(isinstance(row['sha256'], str) and re.fullmatch('[0-9a-f]{64}', row['sha256']) is not None, 'bad digest')
        rows[name] = row
    require(list(rows) == sorted(rows), 'unsorted files')
    dirs = [safe(d) for d in m['directories']]
    require(dirs == sorted(set(dirs)), 'duplicate/unsorted directories')
    files_actual, dirs_actual = set(), set()
    for base, ds, fs in os.walk(root, followlinks=False):
        for name in ds + fs:
            p = Path(base) / name
            rel = safe(p.relative_to(root).as_posix())
            mode = p.lstat().st_mode
            require(not stat.S_ISLNK(mode), 'symlink: ' + rel)
            if stat.S_ISDIR(mode):
                dirs_actual.add(rel)
            else:
                require(stat.S_ISREG(mode), 'nonregular: ' + rel)
                files_actual.add(rel)
    require(files_actual == set(rows) | {'review-manifest.json'}, 'exact file membership')
    require(dirs_actual == set(dirs), 'exact directory membership')
    for name, row in rows.items():
        data = (root / name).read_bytes()
        require(len(data) == row['bytes'] and sha(data) == row['sha256'], 'payload mismatch: ' + name)
    return {'result': 'PASS_INTEGRITY_ONLY', 'files': len(rows), 'directories': len(dirs), 'writes': 0, 'mathematics_certified_by_hash': False}

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--anchor', required=True)
    ap.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    args = ap.parse_args()
    try:
        print(json.dumps(verify(args.root.absolute(), args.anchor), sort_keys=True))
    except (ValueError, KeyError, TypeError, OSError) as exc:
        print('INTEGRITY_REJECT: ' + str(exc))
        raise SystemExit(1)
