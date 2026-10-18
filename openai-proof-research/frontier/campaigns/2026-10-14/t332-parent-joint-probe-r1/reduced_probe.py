#!/usr/bin/env python3
"""MIT. Prespecified reproducible subsampling after full LP timeouts."""
from pathlib import Path
import json,random
from probe import solve
rng=random.Random(3322026)
for line in (Path(__file__).parent/'structured-results.jsonl').read_text().splitlines():
 case=json.loads(line);indices=sorted(rng.sample(range(len(case['points'])),24));points=[case['points'][i] for i in indices]
 result=solve(case['parent'],case['weights'],case['anchors'],points)
 print(json.dumps({'name':case['name'],'point_indices':indices,'result':result,'limits':'Only24 selected unknown points, not the full cube; other inputs unchanged.'}),flush=True)
