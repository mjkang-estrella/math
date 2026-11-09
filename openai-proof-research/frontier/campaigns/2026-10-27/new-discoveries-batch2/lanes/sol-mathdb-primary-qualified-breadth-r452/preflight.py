from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent; B=L.parent
bindings={}
def bind(p,sha=None,size=None):
 p=Path(p).resolve(); b=p.read_bytes(); h=hashlib.sha256(b).hexdigest()
 assert sha is None or sha==h,(str(p),'hash')
 assert size is None or size==len(b),(str(p),'size')
 bindings[str(p)]={'original':str(p),'sha256':h,'bytes':len(b)}
 return b
for name in ['root-mathdb-breadth-intake-r451','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363','pi-mathdb-full-corpus-inventory-r301']:
 d=B/name; m=json.loads(bind(d/'manifest.json')); rows=m if isinstance(m,list) else m['files']
 if name.startswith('pi-'):
  chunks=[r for r in rows if r['path'].startswith('corpus/mathdb-normalized-chunk-')]; assert len(chunks)==20
  assert {r['path'] for r in chunks}=={str(p.relative_to(d)) for p in (d/'corpus').glob('mathdb-normalized-chunk-*.jsonl')}
  for r in chunks:bind(d/r['path'],r['sha256'],r['bytes'])
  frozen=m.get('frozen_inputs',[])
  assert {r["path"] for r in frozen}=={str(p.relative_to(d)) for p in (d/"frozen").rglob("*") if p.is_file()}
  for r in frozen:bind(d/r["path"],r["sha256"],r["bytes"])
  (L/'inventory-frozen-membership.json').write_text(json.dumps(frozen,indent=2)+'\n')
 else:
  for r in rows: bind(d/r['path'],r['sha256'],r.get('size',r.get('bytes')))
  if (d/'bindings.json').exists():
   for r in json.loads(bind(d/'bindings.json')):
    if 'original' in r: bind(r['original'],r['sha256'],r.get('size',r.get('bytes')))
# Applicable policy and guard frozen before any scientific reading.
for p in [B.parent/'AGENTS.md',B.parents[4]/'AGENTS.md',B/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:
 if p.exists():bind(p)
for p in [B.parent/'ledger.json',B.parent/'prior-campaign-context.json',B.parents[4]/'sources/upstream.json',B.parents[4]/'sources/CONTENTS.md']:
 if p.exists():bind(p)
(L/'bindings.json').write_text(json.dumps(list(bindings.values()),indent=2)+'\n')
(L/'preflight.json').write_text(json.dumps({'integrity':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'flat_bound_files':len(bindings),'chunks_verified_in_place':20,'upstream_code_executed':False},indent=2)+'\n')
print('PASS',len(bindings),'flat inputs; twenty chunks')
