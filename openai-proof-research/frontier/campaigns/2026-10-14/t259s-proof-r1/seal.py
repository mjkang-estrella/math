#!/usr/bin/env python3
"""Writes manifest.json for the review packet (exact inventory). MIT. Run only by the review owner."""
import hashlib, json, os, sys
from pathlib import Path
root = Path(sys.argv[1]).resolve()
files, dirs = {}, []
for dp, dn, fn in os.walk(root):
    dn.sort()
    for d in dn:
        dirs.append((Path(dp) / d).relative_to(root).as_posix())
    for f in fn:
        p = Path(dp) / f
        rel = p.relative_to(root).as_posix()
        if rel != 'manifest.json':
            files[rel] = {'bytes': p.stat().st_size, 'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
m = {'schema': 'exact-inventory-v1', 'packet': 't259s-proof-r1', 'verdict': 'PASS_FULL_T259S',
     'reviewed_author_manifest': 'ff6bd1361506423bf135661e6d930e3635700f14db2de9471548afafc730454d',
     'reviewed_author_verifier': '245d3b949fa26a6ae42d214cef89c59a0d425ec8d366c746f69122e9b671d54d',
     'counted': False, 'files': dict(sorted(files.items())), 'directories': sorted(dirs)}
(root / 'manifest.json').write_text(json.dumps(m, sort_keys=True, indent=2) + '\n')
