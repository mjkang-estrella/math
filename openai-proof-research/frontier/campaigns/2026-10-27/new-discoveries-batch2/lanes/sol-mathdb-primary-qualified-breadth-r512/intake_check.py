import json,hashlib,pathlib,datetime
P=pathlib.Path(__file__).resolve().parent; L=P.parent; I=L/'root-mathdb-breadth-intake-r511'; C=L/'pi-mathdb-full-corpus-inventory-r301'
def sha(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text())
def dump(n,o):(P/n).write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n')
bindings={}
def bind(p,expected=None):
 p=p.resolve(); b=p.read_bytes(); d={'path':str(p),'size':len(b),'sha256':sha(b)}
 if expected:assert d['size']==expected.get('size',expected.get('bytes')) and d['sha256']==expected['sha256'],str(p)
 bindings[str(p)]=d;return b
bind(I/'manifest.json',{'size':9343,'sha256':'8f5c8b94a76615c305640af91caf1f43ca31fcede1c0ba678d1033e29836cfc6'})
m=load(I/'manifest.json'); expected={e['path'] for e in m['files']}
assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}==expected|set(m['excluded_exact_paths'])
for e in m['files']:bind(I/e['path'],e)
bind(I/'verification-receipt.json',{'size':391,'sha256':'8c7cecf97b5084610c662f59e311c5984f6f3d5c5c2d3b7b14f75cc881a80e7e'})
pairs=load(I/'bindings.json')
for e in pairs:
 assert bind(pathlib.Path(e['original']),e)==bind(pathlib.Path(e['copy']),e)
cm=load(C/'manifest.json'); chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:bind(C/e['path'],e)
for n in ['root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','root-mathdb-accepted-exclusions-r304/historical-dispositions.json','root-mathdb-cayley-review-intake-r363/DECISION.md'] :bind(L/n)
for n in ['ledger.json','prior-campaign-context.json']:bind(L.parent/n)
for p in [L.parents[4]/'sources/upstream.json',L.parents[4]/'sources/CONTENTS.md',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',L.parents[4]/'AGENTS.md',L.parent/'AGENTS.md']:
 if p.exists():bind(p)
q=load(I/'queue.json');r=load(I/'reserved-ids.json');cov=load(I/'coverage-delta.json');active=load(I/'active-breadth-reservations.json')
ids=[e['mathdb_id'] for e in q];assert len(ids)==len(set(ids))==50 and set(ids)==set(r['ids']) and len(cov)==3833
assert next(e['ids'] for e in active if e['lane']==P.name)==ids
sets=[set(ids)]+[set(e['ids']) for e in active if e['lane']!=P.name]
assert len(sets)==3
for j,s in enumerate(sets):
 assert len(s)==50 and not s&set(map(int,cov)) and not s&set(r['protected_ids'])
 for t in sets[j+1:]:assert not s&t
assert set.union(*sets[1:])==set(r['other_active_reservations'])
dump('flat-bindings.json',list(bindings.values()))
rows=[]
for e in chunks:
 for line,b in enumerate((C/e['path']).read_bytes().splitlines(),1):
  rec=json.loads(b)
  if rec['mathdb_id'] in ids:
   rows.append({'mathdb_id':rec['mathdb_id'],'corpus_path':str(C/e['path']),'line':line,'statement':rec['statement'],'statement_sha256':sha(rec['statement'].encode()),'canonical_record_sha256':sha(json.dumps(rec,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()),'record':rec})
assert len(rows)==50
rows.sort(key=lambda x:ids.index(x['mathdb_id']));dump('statements.json',rows)
dump('intake-verification.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'intake_exact_payload':True,'direct_pairs':len(pairs),'original_chunks':20,'frozen_inputs':8,'baseline':3833,'disjoint_sets':[len(s) for s in sets],'read_only_upstream_verifier_executed':False})
print('PASS: intake, direct pairs, 20 original chunks, 8 inputs, 3833 baseline and three disjoint reservations; 50 extracted')
