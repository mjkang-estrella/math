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
m = {'schema': 'exact-inventory-v1', 'packet': 't337e-proof-r1', 'verdict': 'NOT_PASS_R1_REQUIRED_REPAIR',
     'required_objections': ['R1'], 'optional_objections': ['O%d' % i for i in range(1, 10)],
     'reviewed_author_manifest': '701a9549aa13d547f101ef9dd4ff3c890274384fef4020f6d20bc8b4c7faaa20',
     'reviewed_author_verifier': '83d413570b7385364bfa444e6eae9525412e22cfc7dcb3e8560a171c114c3ba8',
     'reviewed_proof': '0b8a1c15141ac264c538ab97da429b1f2390878e1c7f9b089dc52c3cd5bc7a5d',
     'reviewed_scope': 'f16d3a1ad0c6e777151f2c1862e2a4f560b93272dadc31b102769d3066da70b9',
     'counted': False, 'files': dict(sorted(files.items())), 'directories': sorted(dirs)}
(root / 'manifest.json').write_text(json.dumps(m, sort_keys=True, indent=2) + '\n')
