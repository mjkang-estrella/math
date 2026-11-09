from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent; B=L.parent
H=lambda b:hashlib.sha256(b).hexdigest()
refs={}
def bind(p,expected=None):
 p=Path(p); b=p.read_bytes(); row={'path':str(p),'size':len(b),'sha256':H(b)}
 if expected:
  assert row['sha256']==expected['sha256'],str(p)
  assert row['size']==expected.get('size',expected.get('bytes',row['size'])),str(p)
 refs[str(p)]=row
 return b
def manifest(name):
 d=B/name; m=json.loads(bind(d/'manifest.json'))
 for r in (m if isinstance(m,list) else m['files']):bind(d/r['path'],r)
 return m
im=manifest('root-mathdb-breadth-intake-r457')
I=B/'root-mathdb-breadth-intake-r457'
for r in json.loads((I/'bindings.json').read_text()):
 bind(r['original'],r);bind(r['copy'],r)
vm=json.loads(bind(B/'pi-mathdb-full-corpus-inventory-r301/manifest.json'))
chunks=[r for r in vm['files'] if r['path'].startswith('corpus/') and r['path'].endswith('.jsonl')]
assert len(chunks)==20
for r in chunks:bind(B/'pi-mathdb-full-corpus-inventory-r301'/r['path'],r)
for name in ['root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:manifest(name)
for p in [B.parent/'ledger.json',B.parent/'prior-campaign-context.json',B.parents[4]/'sources/upstream.json',B.parents[4]/'sources/CONTENTS.md']:
 if p.exists():bind(p)
for p in [B.parents[4]/'AGENTS.md',B.parent/'AGENTS.md',B/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:
 if p.exists():bind(p)
rows=sorted(refs.values(),key=lambda r:r['path'])
(L/'frozen_inputs.json').write_text(json.dumps(rows,indent=2)+'\n')
(L/'bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
(L/'freeze-receipt.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','files':len(rows),'chunks':20,'frozen_inputs_sha256':H((L/'frozen_inputs.json').read_bytes()),'method':'independent byte/hash comparisons; no upstream executable run; flat references only'},indent=2)+'\n')
print('FREEZE PASS',len(rows))
for f in ['coverage-delta.json','reserved-ids.json']:
 j=json.loads((I/f).read_text());print(f, list(j) if isinstance(j,dict) else type(j))
for f in ['accepted-exclusions.json','historical-dispositions.json']:
 j=json.loads((B/'root-mathdb-accepted-exclusions-r304'/f).read_text());print(f,str(j)[:1400])
