#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parents[3];E=Path(__file__).resolve().parent
S=R/'frontier/sources/i30_einstein_metric_stability_r2'
seal=S/'artifact-seal.json'
excluded={seal,E/'verification.json'}
paths=[R/'frontier/reviews/i30-einstein-metric-stability-r2.md']
for directory in [S,E]:paths.extend(p for p in directory.rglob('*') if p.is_file() and p not in excluded and '__pycache__' not in p.parts)
rows=[dict(path=str(p.relative_to(R)),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in sorted(paths)]
if '--verify' in sys.argv:
    assert rows==json.loads(seal.read_text())['files'],'Review artifact seal mismatch'
    print(json.dumps(dict(status='PASS',sealed_artifacts=len(rows))))
else:
    seal.write_text(json.dumps(dict(algorithm='sha256',excluded=['artifact-seal.json','verification.json','__pycache__'],files=rows),indent=2)+'\n')
    print(json.dumps(dict(status='SEALED',sealed_artifacts=len(rows))))
