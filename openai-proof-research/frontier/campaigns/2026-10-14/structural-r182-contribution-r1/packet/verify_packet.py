#!/usr/bin/env python3
"""Read-only artifact verifier; run from the actual project root. No mathematical gate."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import stat


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(ok, message):
    if not ok:
        raise ValueError(message)


def verify(root, final_anchor, manifest_anchor, report_anchor, originals=False):
    packet = root / 'packet'
    for path, anchor in [(root/'FINAL.json', final_anchor), (packet/'MANIFEST.json', manifest_anchor), (root/'REPORT.md', report_anchor)]:
        require(len(anchor) == 64 and all(c in '0123456789abcdef' for c in anchor), 'invalid explicit anchor')
        require(not path.is_symlink(), 'symlink anchor')
        require(sha(path) == anchor, 'detached anchor mismatch: '+str(path))
    manifest = json.loads((packet/'MANIFEST.json').read_text())
    names = set()
    for entry in manifest['members']:
        name = entry['path']
        rel = Path(name)
        require(not rel.is_absolute() and '..' not in rel.parts and name != 'MANIFEST.json', 'unsafe member')
        require(name not in names, 'duplicate member')
        names.add(name)
        path = packet/rel
        require(not path.is_symlink() and path.is_file(), 'missing or symlink member: '+name)
        require(path.stat().st_size == entry['bytes'], 'member size mismatch: '+name)
        require(sha(path) == entry['sha256'], 'member hash mismatch: '+name)
    actual = set()
    for base, dirs, files in os.walk(packet, followlinks=False):
        for name in dirs:
            require(not (Path(base)/name).is_symlink(), 'symlink directory')
        for name in files:
            path = Path(base)/name
            require(not path.is_symlink(), 'symlink file')
            actual.add(path.relative_to(packet).as_posix())
    require(actual == names | {'MANIFEST.json'}, 'exact membership mismatch')
    if originals:
        project = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
        require(Path.cwd().resolve() == project, 'run from actual project root')
        original_dir = project/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r182'
        for name, digest in [
            ('FROZEN-THEOREM.md','62b6ad633a662a491be617e82f8eb441be8f02069a7dc5289c10996dc8d9bee8'),
            ('notes/03-author-proof.md','9f2989669c20bea00260a77dd11a4a4fcb1e7cb0d84f75f8777871ae85d1d38e')
        ]:
            path = original_dir/name
            require(sha(path) == digest, 'original byte mismatch: '+name)
            require(stat.S_IMODE(path.stat().st_mode) == 0o644, 'original mode mismatch: '+name)
        for name in ['REVIEW.md','READING-ISOLATION.md']:
            require((root/name).read_bytes() == (packet/name).read_bytes(), 'outside review copy mismatch')
        for name, expected in [('main.tex','ab9bd82b388ec4e55a333d05c61c853b7941798b'),('references.tex','796debae8df956385c1aee3398c3d578fda1cdf5')]:
            body = (packet/'private'/name).read_bytes()
            blob = hashlib.sha1(b'blob '+str(len(body)).encode()+b'\0'+body).hexdigest()
            require(blob == expected, 'pinned source blob mismatch')
    return {'artifact_verification':'MATCH','members':len(names),'explicit_originals_checked':originals,'mathematical_gate':False}


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', required=True, type=Path)
    ap.add_argument('--final-sha256', required=True)
    ap.add_argument('--manifest-sha256', required=True)
    ap.add_argument('--report-sha256', required=True)
    ap.add_argument('--check-originals', action='store_true')
    args = ap.parse_args()
    try:
        print(json.dumps(verify(args.root, args.final_sha256, args.manifest_sha256, args.report_sha256, args.check_originals)))
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(json.dumps({'artifact_verification':'REJECT','error':str(error),'mathematical_gate':False}))
        raise SystemExit(1)
