#!/usr/bin/env python3
"""Seal this review, its snapshots, and its unchanged live dependencies."""
from pathlib import Path
import hashlib,json,sys
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i15_odd_order_topology_r2'
E=ROOT/'frontier/experiments/i15_odd_order_topology_r2'
REPORT=ROOT/'frontier/reviews/i15-odd-order-topology-r2.md'
MAN=S/'artifact-manifest.json'
def digest(p):
 b=p.read_bytes(); return dict(path=str(p.relative_to(ROOT)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def files(): return sorted([REPORT]+[p for d in [S,E] for p in d.rglob('*') if p.is_file() and p!=MAN])
def verify():
 d=json.loads(MAN.read_text()); now=[digest(p) for p in files()]
 assert now==d['files'],'Review artifact list or bytes changed'
 for r in json.loads((S/'dependency-manifest.json').read_text()):
  assert digest(ROOT/r['path'])=={k:r[k] for k in ['path','bytes','sha256']},r['path']
  assert (ROOT/r['path']).read_bytes()==(ROOT/r['snapshot']).read_bytes(),r['path']
 print(json.dumps(dict(status='PASS',sealed_review_files=len(now),unchanged_dependencies=len(json.loads((S/'dependency-manifest.json').read_text())),report_sha256=digest(REPORT)['sha256']),indent=2))
if '--verify' in sys.argv: verify()
else:
 MAN.write_text(json.dumps(dict(schema=1,scope='Independent proof R2. All pinned results stipulated true; integrity is not proof.',files=[digest(p) for p in files()]),indent=2)+'\n'); verify()
