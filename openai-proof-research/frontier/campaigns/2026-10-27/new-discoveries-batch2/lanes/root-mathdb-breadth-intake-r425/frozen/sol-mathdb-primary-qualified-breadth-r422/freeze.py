import json,hashlib,pathlib
L=pathlib.Path('frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes').resolve(); O=L/'sol-mathdb-primary-qualified-breadth-r422'; R=L/'root-mathdb-breadth-intake-r421'; I=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
bindings={}
def bind(p,sha=None,size=None):
 p=p.resolve(); s=p.stat().st_size; h=digest(p)
 assert sha is None or sha==h,(p,'sha'); assert size is None or size==s,(p,'size')
 bindings[str(p)]={'original':str(p),'sha256':h,'size':s}
for x in load(R/'manifest.json')['files']:bind(R/x['path'],x['sha256'],x['size'])
bind(R/'manifest.json')
for x in load(R/'bindings.json'):bind(pathlib.Path(x['original']),x['sha256'],x['size'])
m=load(I/'manifest.json');chunks=[x for x in m['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20
for x in chunks:bind(I/x['path'],x['sha256'],x['bytes'])
for lane,files in [('root-mathdb-accepted-exclusions-r304',['manifest.json','accepted-exclusions.json','historical-dispositions.json']),('root-mathdb-cayley-review-intake-r363',['manifest.json','disposition.json','reserved-ids.json'])]:
 for name in files:bind(L/lane/name)
for p in [pathlib.Path('AGENTS.md'), L.parent/'AGENTS.md',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',pathlib.Path('sources/upstream.json'),pathlib.Path('sources/CONTENTS.md'),L.parent/'ledger.json',L.parent/'prior-campaign-context.json']:bind(p)
(O/'bindings.json').write_text(json.dumps(list(bindings.values()),indent=2)+'\n')
ids=load(R/'reserved-ids.json')['ids'];records=[]
for x in chunks:
 with (I/x['path']).open() as f:
  for line in f:
   # Filter before parsing so no unrelated record body is inspected.
   if any(('"mathdb_id": '+str(i)) in line or ('"mathdb_id":'+str(i)) in line for i in ids):
    r=json.loads(line)
    if r['mathdb_id'] in ids:records.append(r)
assert len(records)==50,len(records)
(O/'selected-records.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n')
(O/'freeze-receipt.json').write_text(json.dumps({'bindings':len(bindings),'chunks':20,'records':50,'upstream_verifiers_executed':False},indent=2)+'\n')
print('bound',len(bindings),'records',len(records)); print('keys',records[0].keys())
