#!/usr/bin/env python3
"""Create only the I51 seal. Never invoked by the read-only verifier."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i51_hard_moment_quantitative_stability_novelty'
E=R/'frontier/experiments/i51_hard_moment_quantitative_stability_novelty'
report=R/'frontier/reviews/i51-hard-moment-quantitative-stability-novelty.md'
files=sorted({p for root in [S,E] for p in root.rglob('*') if p.is_file()}|{report})
rows=[]
for p in files:
 if p==S/'artifact-seal.json':continue
 b=p.read_bytes();rows.append(dict(path=str(p.relative_to(R)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
(S/'artifact-seal.json').write_text(json.dumps(dict(pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',scope='I51 artifacts only; integrity is not proof approval',files=rows),indent=2)+'\n')
print(json.dumps(dict(I51_artifacts=len(rows))))
