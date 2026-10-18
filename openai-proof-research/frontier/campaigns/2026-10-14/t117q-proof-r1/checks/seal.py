#!/usr/bin/env python3
"""MIT. Builds the strict exact-inventory manifest for the review packet and prints its SHA256.
With --out, writes the manifest elsewhere (used for pre-seal copied controls)."""
import argparse, hashlib, json, stat
from pathlib import Path

ap = argparse.ArgumentParser(); ap.add_argument('--out', type=Path); a = ap.parse_args()
p = Path(__file__).absolute().parents[1]
files, dirs = [], ['.']
for f in sorted(p.rglob('*')):
    s = f.lstat(); rel = f.relative_to(p).as_posix()
    if stat.S_ISDIR(s.st_mode):
        dirs.append(rel)
    elif stat.S_ISREG(s.st_mode):
        assert s.st_nlink == 1, rel
        if rel != 'MANIFEST.json':
            b = f.read_bytes(); files.append({'path': rel, 'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest()})
    else:
        raise ValueError('nonregular node ' + rel)
m = {'schema': 'strict-exact-inventory-v1', 'packet': 't117q-proof-r1',
     'status': 'Independent T117Q proof review round 1: PASS_FULL_T117Q; proof verdict only, no contribution/acceptance/count verdict',
     'author_manifest_sha256': '053986e5a446cd18251b3e3e8b917bc58cafb0f68d6de87562fe190766e28ae2',
     'directories': sorted(dirs), 'files': files}
b = (json.dumps(m, indent=2) + '\n').encode()
(a.out or p / 'MANIFEST.json').write_bytes(b)
print(hashlib.sha256(b).hexdigest())
