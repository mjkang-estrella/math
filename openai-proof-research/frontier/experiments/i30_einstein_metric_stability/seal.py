#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i30_einstein_metric_stability';E=R/'frontier/experiments/i30_einstein_metric_stability'
seal=S/'artifact-seal.json';excluded={seal,E/'verification.json'}
paths=[R/'frontier/iterations/i30-einstein-metric-stability.md']
for d in [S,E]:paths.extend(p for p in d.rglob('*') if p.is_file() and p not in excluded and '__pycache__' not in p.parts)
rows=[dict(path=str(p.relative_to(R)),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in sorted(paths)]
if '--verify' in sys.argv:
 old=json.loads(seal.read_text())['files'];assert rows==old,'Artifact seal mismatch'
 print(json.dumps({'status':'PASS','sealed_artifacts':len(rows),'scope':'Only designated I30 files; reused read-only dependencies verified separately.'}))
else:
 seal.write_text(json.dumps({'algorithm':'sha256','excluded':['artifact-seal.json','verification.json','__pycache__'],'files':rows},indent=2)+'\n');print('Sealed',len(rows),'artifacts')
