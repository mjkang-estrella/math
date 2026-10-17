#!/usr/bin/env python3
"""Offline, read-only verifier. Integrity is neither proof nor a novelty verdict."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys


def sha(b):
    return hashlib.sha256(b).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--manifest-sha256', required=True)
    args = ap.parse_args()
    root = Path(__file__).resolve().parent
    assert re.fullmatch('[0-9a-f]{64}', args.manifest_sha256), 'invalid external anchor'
    manifest = root / 'inventory.json'
    assert not manifest.is_symlink(), 'manifest link'
    raw = manifest.read_bytes()
    assert sha(raw) == args.manifest_sha256, 'external anchor mismatch'
    inv = json.loads(raw)
    files, dirs = {}, []
    for p in sorted(root.rglob('*')):
        assert not p.is_symlink(), 'link: ' + str(p)
        rel = p.relative_to(root).as_posix()
        if p.is_dir():
            dirs.append(rel)
        else:
            assert p.is_file(), 'nonregular object: ' + rel
            if rel != 'inventory.json':
                b = p.read_bytes()
                files[rel] = {'bytes': len(b), 'sha256': sha(b)}
    assert files == inv['files'], 'exact file inventory mismatch'
    assert dirs == inv['directories'], 'exact directory inventory mismatch'

    def read(rel):
        q = PurePosixPath(rel)
        assert not q.is_absolute() and '..' not in q.parts and rel in files
        return (root / rel).read_bytes()

    for r in json.loads(read('source-receipts.json')):
        b = read(r['path'])
        assert len(b) == r['bytes'] and sha(b) == r['sha256']
        assert hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest() == r['git_blob']
        assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in r['url']
    for r in json.loads(read('primary-receipts.json')):
        rel = r.get('pdf', r.get('path'))
        b = read(rel)
        assert b.startswith(b'%PDF') and len(b) == r['bytes'] and sha(b) == r['sha256']
        tr = r.get('text_path', str(PurePosixPath(rel).with_suffix('.txt')))
        assert sha(read(tr)) == r['text_sha256']
    saved_context = 0
    for r in json.loads(read('context-receipts.json')):
        if r['snapshot'] is not None:
            b = read(r['snapshot'])
            assert len(b) == r['bytes'] and sha(b) == r['sha256']
            saved_context += 1
    diagnostic = subprocess.run([sys.executable, '-B', str(root / 'affine_checks.py')],
                                capture_output=True, check=True, timeout=30)
    assert diagnostic.stdout == read('affine-checks.json'), 'diagnostic reproduction mismatch'
    print(json.dumps({'status': 'PASS_INTEGRITY_AND_FINITE_REPRODUCTION',
                      'manifest_sha256': args.manifest_sha256,
                      'files': len(files), 'directories': len(dirs),
                      'pinned_sources': 17, 'primary_pdfs': 5,
                      'saved_context_snapshots': saved_context,
                      'mathematical_or_contribution_verdict': False}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except Exception as exc:
        print('FAIL: ' + str(exc), file=sys.stderr)
        sys.exit(1)
