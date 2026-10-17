#!/usr/bin/env python3
"""Read-only exact-membership verifier. Original code: Myeongjin Kang, MIT.
Authenticates bytes only; does not execute source code or certify mathematics.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def pairs_unique(pairs):
    out = {}
    for key, value in pairs:
        require(key not in out, 'duplicate JSON key')
        out[key] = value
    return out


def parse(data):
    def bad_constant(value):
        raise ValueError('nonfinite JSON constant: ' + value)
    return json.loads(data, object_pairs_hook=pairs_unique, parse_constant=bad_constant)


def canonical(name):
    require(isinstance(name, str) and name and '\\' not in name, 'invalid path')
    p = PurePosixPath(name)
    require(not p.is_absolute() and p.as_posix() == name, 'noncanonical path')
    require(all(x not in ('', '.', '..', '__pycache__') for x in p.parts), 'unsafe path')
    require(not name.endswith(('.pyc', '.pyo')), 'bytecode is forbidden')
    return name


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--anchor', required=True, help='Externally supplied output-manifest SHA256')
    args = ap.parse_args()
    require(re.fullmatch(r'[0-9a-f]{64}', args.anchor) is not None, 'invalid anchor')
    here = Path(__file__).absolute()
    require(not here.is_symlink(), 'verifier symlink')
    root = here.parent
    require(not root.is_symlink(), 'root symlink')
    manifest_path = root / 'output-manifest.json'
    require(manifest_path.is_file() and not manifest_path.is_symlink(), 'invalid manifest')
    raw = manifest_path.read_bytes()
    require(sha(raw) == args.anchor, 'external manifest anchor mismatch')
    # No payload JSON is parsed before external authentication.
    m = parse(raw)
    require(m['schema'] == 'CM275-exact-membership-v1', 'schema mismatch')
    expected = {}
    for rec in m['files']:
        name = canonical(rec['path'])
        require(name != 'output-manifest.json' and name not in expected, 'duplicate/self file')
        require(type(rec['bytes']) is int and rec['bytes'] >= 0, 'invalid size')
        require(re.fullmatch(r'[0-9a-f]{64}', rec['sha256']) is not None, 'invalid digest')
        expected[name] = rec
    directories = [canonical(x) for x in m['directories']]
    require(len(set(directories)) == len(directories), 'duplicate directory')
    actual_files, actual_dirs = set(), set()
    for folder, dirs, files in os.walk(root, followlinks=False):
        for name in dirs + files:
            path = Path(folder) / name
            rel = canonical(path.relative_to(root).as_posix())
            mode = path.lstat().st_mode
            require(not stat.S_ISLNK(mode), 'symlink: ' + rel)
            if stat.S_ISDIR(mode):
                actual_dirs.add(rel)
            else:
                require(stat.S_ISREG(mode), 'nonregular file: ' + rel)
                actual_files.add(rel)
    require(actual_files == set(expected) | {'output-manifest.json'}, 'file membership mismatch')
    require(actual_dirs == set(directories), 'directory membership mismatch')
    for name, rec in expected.items():
        data = (root / name).read_bytes()
        require(len(data) == rec['bytes'] and sha(data) == rec['sha256'], 'payload mismatch: ' + name)

    inputs = parse((root / 'input-manifest.json').read_bytes())
    require(inputs['pin'] == 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb', 'pin mismatch')
    source_names = set()
    for rec in inputs['pinned_blobs']:
        name = canonical(rec['local'])
        require(name in expected and name not in source_names, 'source membership mismatch')
        source_names.add(name)
        data = (root / name).read_bytes()
        require(sha(data) == rec['sha256'] and len(data) == rec['bytes'], 'source digest mismatch')
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        require(blob == rec['git_blob'], 'Git blob mismatch')
        require(rec['url'] == 'https://raw.githubusercontent.com/openai/math/' + inputs['pin'] + '/' + rec['path'], 'source URL mismatch')
    for rec in inputs['primary_pdfs']:
        name = canonical(rec['local'])
        require(name in expected, 'primary membership mismatch')
        data = (root / name).read_bytes()
        require(data.startswith(b'%PDF-'), 'primary is not a PDF')
        require(sha(data) == rec['sha256'] and len(data) == rec['bytes'], 'primary digest mismatch')
    freeze = parse((root / 'freeze-receipt.json').read_bytes())
    require(sha((root / 'original-scope.md').read_bytes()) == freeze['scope_sha256'], 'scope changed after freeze')
    for name, digest in freeze['prefreeze_files'].items():
        require(canonical(name) in expected and sha((root / name).read_bytes()) == digest, 'pre-freeze file changed')
    require(m['scope_sha256'] == freeze['scope_sha256'], 'manifest scope mismatch')
    require(m['candidate_sha256'] == sha((root / 'candidate.md').read_bytes()), 'candidate mismatch')
    print(json.dumps({'result': 'INTEGRITY_OK_ONLY', 'payloads': len(expected),
                      'directories': len(directories), 'pinned_blobs': len(source_names),
                      'primary_pdfs': len(inputs['primary_pdfs']), 'writes': 0,
                      'mathematical_programs_executed': False,
                      'proof_verdict': None, 'contribution_verdict': None}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError, json.JSONDecodeError) as exc:
        print('INTEGRITY_REJECT: ' + str(exc), file=sys.stderr)
        sys.exit(1)
