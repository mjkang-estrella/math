#!/usr/bin/env python3
"""Seal only the uniquely owned I50 artifact set; never refresh any old seal."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i50_hard_moment_quantitative_stability_r2';E=R/'frontier/experiments/i50_hard_moment_quantitative_stability_r2';p=S/'artifact-seal.json'
files=[R/'frontier/reviews/i50-hard-moment-quantitative-stability-r2.md']
files += [x for root in [S,E] for x in root.rglob('*') if x.is_file() and x!=p]
rows=[]
for f in sorted(files):
 b=f.read_bytes();rows.append({'path':str(f.relative_to(R)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
p.write_text(json.dumps({'pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','scope':'I50 only; integrity seal is not analytic proof approval','files':rows},indent=2)+'\n')
print(json.dumps({'sealed_artifacts':len(rows)}))
