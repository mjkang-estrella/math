#!/usr/bin/env python3
"""Read-only artifact verifier; not a mathematical or contribution test."""
import argparse, hashlib, json, os, re, stat, sys
from pathlib import Path, PurePosixPath

OUTSIDE = {'FINAL.json', 'MANIFEST.json', 'REPORT.md'}
SCOPE = 'fc1e349511e87ebd6a0ba0c1533b2c8a81e5fca100e30e9ef2ad7cf5915f002b'

def require(ok, message):
    if not ok:
        raise ValueError(message)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON key: ' + key)
        result[key] = value
    return result

def read_json(path):
    return json.loads(path.read_text(), object_pairs_hook=unique)

def safe(name):
    p = PurePosixPath(name)
    require(name and not p.is_absolute() and '..' not in p.parts and '.' not in p.parts and str(p) == name, 'unsafe path')

def regular(path):
    s = path.lstat()
    require(stat.S_ISREG(s.st_mode) and s.st_nlink == 1, 'not regular single-link file: ' + str(path))
    return s

def inventory(root):
    require(stat.S_ISDIR(root.lstat().st_mode), 'root must be a real directory')
    files, directories = {}, {}
    for base, dirs, names in os.walk(root, followlinks=False):
        for name in sorted(dirs + names):
            p = Path(base) / name
            rel = p.relative_to(root).as_posix()
            s = p.lstat()
            require(not stat.S_ISLNK(s.st_mode), 'symlink: ' + rel)
            if stat.S_ISDIR(s.st_mode):
                directories[rel] = stat.S_IMODE(s.st_mode)
            else:
                regular(p)
                if rel not in OUTSIDE:
                    files[rel] = {'bytes': s.st_size, 'mode': stat.S_IMODE(s.st_mode), 'sha256': digest(p)}
    return {'root_mode': stat.S_IMODE(root.lstat().st_mode), 'files': files, 'directories': directories}

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True)
    for name in ['final', 'manifest', 'report']:
        ap.add_argument('--' + name + '-sha256', required=True)
    a = ap.parse_args()
    root = Path(a.root)
    for key, name in [('final', 'FINAL.json'), ('manifest', 'MANIFEST.json'), ('report', 'REPORT.md')]:
        h = getattr(a, key + '_sha256')
        require(re.fullmatch('[0-9a-f]{64}', h) is not None, 'full detached SHA256 required')
        regular(root / name)
        require(digest(root / name) == h, 'detached anchor mismatch: ' + name)
    final = read_json(root / 'FINAL.json')
    manifest = read_json(root / 'MANIFEST.json')
    require(final['manifest_sha256'] == a.manifest_sha256, 'manifest binding')
    require(final['report_sha256'] == a.report_sha256, 'outside REPORT binding')
    require(final['scope_sha256'] == SCOPE == digest(root / 'public/SCOPE.md'), 'unchanged full scope binding')
    require(final['review_sha256'] == digest(root / 'public/REVIEW.md'), 'review prose binding')
    require(final['contribution'] == 'TECHNICAL_CONDITIONAL_ON_CORRECTNESS', 'unexpected contribution field')
    require(final['correctness_gate'] == 'NOT_PERFORMED', 'unexpected correctness gate')
    for name in list(manifest['files']) + list(manifest['directories']):
        safe(name)
    actual = inventory(root)
    require(actual == {key: manifest[key] for key in actual}, 'exact payload inventory/content/mode mismatch')
    print(json.dumps({'artifact_verification': 'PASS', 'payload_files': len(actual['files']), 'payload_directories': len(actual['directories']), 'mathematical_test': False, 'limits': 'Detached anchors, exact retained bytes/modes, real directories and single-link regular files. No external-original monitoring, syscall sandbox, mathematical correctness, priority or acceptance certification.'}, sort_keys=True))

if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        sys.exit(1)
