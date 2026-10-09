"""Seal/verify only this assigned review. --verify never writes."""
from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i15_odd_order_topology_novelty_r3'
E=R/'frontier/experiments/i15_odd_order_topology_novelty_r3'
REPORT=R/'frontier/reviews/i15-odd-order-topology-novelty-r3.md'
SEAL=S/'output-seal.json'
def record(p):
 b=p.read_bytes();return {'path':str(p.relative_to(R)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def files():return sorted([REPORT]+[p for root in [S,E] for p in root.rglob('*') if p.is_file() and p!=SEAL and '__pycache__' not in p.parts])
def dependencies():
 paths={x['path'] for x in json.loads((S/'input-manifest.json').read_text())}
 paths.update(x['snapshot'] for x in json.loads((R/'frontier/sources/i15_odd_order_topology/pinned-manifest.json').read_text()))
 paths.add('frontier/sources/i15_odd_order_topology_r2/output-seal.json') if (R/'frontier/sources/i15_odd_order_topology_r2/output-seal.json').exists() else None
 return [record(R/p) for p in sorted(paths)]
if sys.argv[1:]==['--write']:
 data={'schema':1,'review':'I15 final significance / primary prior art R3','pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','verdict':'TECHNICAL ONLY; full independent proof PASS retained','artifacts':[record(p) for p in files()],'dependencies':dependencies(),'corpus_note':'All 9340 cached text files separately verified by corpus_audit.py against the frozen corpus manifest and complete Git tree. This seal records that manifest; rerun corpus_audit.py to recheck cache bytes.'}
 SEAL.write_text(json.dumps(data,indent=2)+'\n');print(json.dumps({'status':'SEALED','artifacts':len(data['artifacts']),'dependencies':len(data['dependencies']),'report_sha256':record(REPORT)['sha256']}))
elif sys.argv[1:]==['--verify']:
 data=json.loads(SEAL.read_text());assert {x['path'] for x in data['artifacts']}=={str(p.relative_to(R)) for p in files()},'artifact inventory changed'
 for section in ['artifacts','dependencies']:
  for x in data[section]:assert record(R/x['path'])==x,x['path']
 print(json.dumps({'status':'PASS','artifacts':len(data['artifacts']),'unchanged_dependencies':len(data['dependencies']),'report_sha256':record(REPORT)['sha256']},indent=2))
else:raise SystemExit('usage: seal.py --write | --verify')
