#!/usr/bin/env python3
"""Read-only exact-inventory verifier for the T027O formal review r1 (MIT). Identity only."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

INPUT_ANCHOR = 'b35948fddec735c7d9f0ed742d8158f4787f571cd69175a01f4db7ce2add46a4'

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def unique(pairs):
    out = {}
    for k, v in pairs:
        need(k not in out, 'duplicate JSON key')
        out[k] = v
    return out

def safe(name):
    need(isinstance(name, str) and name and '\\' not in name, 'bad path')
    p = PurePosixPath(name)
    need(not p.is_absolute() and p.as_posix() == name and all(x not in ('.', '..') for x in p.parts), 'unsafe path')
    return name

def inventory(root):
    files, dirs = {}, set()
    for base, ds, fs in os.walk(root, followlinks=False):
        for n in ds + fs:
            p = Path(base) / n
            rel = safe(p.relative_to(root).as_posix())
            mode = p.lstat()
            need(not stat.S_ISLNK(mode.st_mode), 'symlink ' + rel)
            if stat.S_ISDIR(mode.st_mode):
                dirs.add(rel)
            else:
                need(stat.S_ISREG(mode.st_mode) and mode.st_nlink == 1, 'nonregular or hardlink ' + rel)
                if rel != 'review-manifest.json':
                    data = p.read_bytes()
                    files[rel] = {'bytes': len(data), 'sha256': sha(data)}
    return files, sorted(dirs)

def verify(root, anchor):
    need(re.fullmatch('[0-9a-f]{64}', anchor) is not None, 'bad anchor')
    need(all(not x.is_symlink() for x in [root] + list(root.parents)), 'symlink root or ancestor')
    m = root / 'review-manifest.json'
    mode = m.lstat()
    need(stat.S_ISREG(mode.st_mode) and mode.st_nlink == 1, 'unsafe manifest')
    raw = m.read_bytes()
    need(sha(raw) == anchor, 'external anchor mismatch')
    manifest = json.loads(raw, object_pairs_hook=unique)
    need(manifest.get('schema') == 'T027O-scoped-formal-review-r1', 'schema')
    need(manifest.get('verdict') == 'PASS_SCOPED_FORMAL_SUPPORT', 'verdict')
    need(manifest.get('full_theorem_formalized') is False, 'scope flag')
    need(manifest.get('input_manifest_sha256') == INPUT_ANCHOR, 'input anchor')
    files, dirs = inventory(root)
    need(files == manifest['files'] and dirs == manifest['directories'], 'exact inventory mismatch')
    receipt = json.loads((root / 'results/independent-build/receipt.json').read_bytes(), object_pairs_hook=unique)
    need(receipt['status'] == 'PASS_INDEPENDENT_BUILD_TYPES_STANDARD_AXIOMS', 'build status')
    need(receipt['sources']['T027OReview.lean'] == files['src/T027OReview.lean']['sha256'], 'review source binding')
    return {'result': 'PASS_REVIEW_IDENTITY_ONLY', 'payload_files': len(files), 'directories': len(dirs)}

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--anchor', required=True)
    ap.add_argument('--root', type=Path, default=Path(__file__).absolute().parent)
    a = ap.parse_args()
    try:
        print(json.dumps(verify(a.root.absolute(), a.anchor), sort_keys=True))
    except (ValueError, KeyError, TypeError, OSError) as e:
        print('INTEGRITY_REJECT: ' + str(e), file=sys.stderr)
        sys.exit(1)
