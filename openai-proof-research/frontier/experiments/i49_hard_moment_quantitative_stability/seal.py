#!/usr/bin/env python3
"""Seal I49 only. This script never reads or refreshes a prior seal for writing."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json,datetime
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i49_hard_moment_quantitative_stability'
E=R/'frontier/experiments/i49_hard_moment_quantitative_stability'
out=S/'artifact-seal.json'
assert not out.exists(),'Existing I49 seal will not be overwritten by this script'
paths=[p for root in [S,E] for p in root.rglob('*') if p.is_file()]
paths.append(R/'frontier/iterations/i49-hard-moment-quantitative-stability.md')
records=[]
for p in sorted(paths):
 b=p.read_bytes();records.append({'path':str(p.relative_to(R)),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)})
out.write_text(json.dumps({'schema':'I49-owned-artifacts-v1','pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',
 'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'scope':'Exact authorized I49 artifact set, excluding this seal itself; no prior seals refreshed.',
 'files':records},indent=2)+'\n')
print(json.dumps({'sealed_artifacts':len(records)}))
