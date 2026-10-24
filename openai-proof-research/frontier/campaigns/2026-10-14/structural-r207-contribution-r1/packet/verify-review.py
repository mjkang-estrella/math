#!/usr/bin/env python3
"""Read-only, explicit-detached-anchor verifier for this review and tiny copies."""
import argparse
import hashlib
import json
import os
import stat
from pathlib import Path, PurePosixPath

EXCLUSIVE = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/structural-r207-contribution-r1')

def require(condition, message):
    if not condition:
        raise ValueError(message)

def regular_bytes(path):
    st = path.lstat()
    require(stat.S_ISREG(st.st_mode), 'not regular: ' + str(path))
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    try:
        chunks = []
        while True:
            data = os.read(fd, 1024 * 1024)
            if not data:
                break
            chunks.append(data)
        return b''.join(chunks)
    finally:
        os.close(fd)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', required=True)
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--report-sha256', required=True)
    args = parser.parse_args()
    root = Path(args.root).absolute()
    require(root == root.resolve(), 'symlink root component')
    require(root == EXCLUSIVE or EXCLUSIVE in root.parents, 'root outside exclusive review namespace')
    manifest_bytes = regular_bytes(root / 'MANIFEST.json')
    require(sha(manifest_bytes) == args.manifest_sha256, 'manifest detached anchor mismatch')
    report_bytes = regular_bytes(root / 'REPORT.md')
    require(sha(report_bytes) == args.report_sha256, 'report detached anchor mismatch')
    final_bytes = regular_bytes(root / 'packet/FINAL.md')
    require(sha(final_bytes) == args.final_sha256, 'final detached anchor mismatch')
    manifest = json.loads(manifest_bytes)
    require(set(manifest) == {'directories', 'files'}, 'manifest schema mismatch')
    require('FINAL.md' in manifest['files'], 'FINAL missing from selection')
    for p in list(manifest['files']) + list(manifest['directories']):
        require(p == '.' or (not PurePosixPath(p).is_absolute() and '..' not in PurePosixPath(p).parts and str(PurePosixPath(p)) == p), 'invalid selected path')
    observed_files, observed_dirs = {}, {}
    def visit(directory, rel):
        st = directory.lstat()
        require(stat.S_ISDIR(st.st_mode), 'not directory: ' + rel)
        observed_dirs[rel] = format(stat.S_IMODE(st.st_mode), '04o')
        for entry in sorted(os.scandir(directory), key=lambda e: e.name):
            p = entry.name if rel == '.' else rel + '/' + entry.name
            est = entry.stat(follow_symlinks=False)
            if stat.S_ISDIR(est.st_mode):
                visit(Path(entry.path), p)
            else:
                require(stat.S_ISREG(est.st_mode), 'nonregular packet member: ' + p)
                data = regular_bytes(Path(entry.path))
                observed_files[p] = {'bytes': len(data), 'mode': format(stat.S_IMODE(est.st_mode), '04o'), 'sha256': sha(data)}
    visit(root / 'packet', '.')
    require(observed_dirs == manifest['directories'], 'packet directory selection or mode mismatch')
    require(set(observed_files) == set(manifest['files']), 'packet file selection mismatch')
    for p, record in observed_files.items():
        require(record == manifest['files'][p], 'packet bytes/hash/mode mismatch: ' + p)
    print(json.dumps({'artifact_match': True, 'files': len(observed_files), 'directories': len(observed_dirs), 'read_only': True, 'correctness': 'UNDISCHARGED', 'scope': 'artifact identity only'}, sort_keys=True))

if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, json.JSONDecodeError) as exc:
        raise SystemExit('ARTIFACT MISMATCH: ' + str(exc))
