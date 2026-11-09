import json,hashlib,pathlib,datetime
O=pathlib.Path(__file__).resolve().parent; L=O.parent; B=L.parent; I=L/'root-mathdb-breadth-intake-r717'; R=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(n,v):(O/n).write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n')
refs={}
def bind(p,sha=None,size=None):
 p=p.resolve(); z={'path':str(p),'sha256':h(p),'size':p.stat().st_size}
 if sha is not None:assert z['sha256']==sha,str(p)
 if size is not None:assert z['size']==size,str(p)
 refs[str(p)]=z
 return z
bind(I/'manifest.json');bind(I/'verification-receipt.json')
m=load(I/'manifest.json'); expected={x['path'] for x in m['files']}|set(m['excluded_exact_paths'])
assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}==expected
for x in m['files']:bind(I/x['path'],x['sha256'],x['size'])
for x in load(I/'bindings.json'):
 for k in ['original','copy']:bind(pathlib.Path(x[k]),x['sha256'],x['bytes'])
m=load(R/'manifest.json'); chunks=[x for x in m['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20
assert len(m['frozen_inputs'])==8
for x in chunks+m['frozen_inputs']:bind(R/x['path'],x['sha256'],x['bytes'])
# Bind flat existing references without expanding historical trees.
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 bind(p)
for p in L.glob('*r363*/*'):
 if p.is_file():bind(p)
q=load(I/'queue-r718.json');r=load(I/'reserved-ids-r718.json');cov=load(I/'coverage-delta.json');assert len(cov)==8833
assert len(q)==len(r['ids'])==50 and {x['mathdb_id'] for x in q}==set(r['ids'])
a=load(I/'active-breadth-reservations.json');print('reservation schemas',[(x.keys(),len(x['ids'])) for x in a])
sets=[set(x['ids']) for x in a]; assert set(r['ids']) in sets
for j,s in enumerate(sets):
 assert not s & set(map(int,cov));assert not s & set(r['protected_ids'])
 for t in sets[:j]:assert not s&t
flat=L/'sol-mathdb-primary-qualified-breadth-r714/flat-bindings.json'
f=load(flat);print('flat schema',str(f)[:150])
dump('flat-bindings.json',list(refs.values()))
dump('pre-reading-checks.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'intake_exact_payload':True,'direct_pairs':len(load(I/'bindings.json')),'corpus_chunks':20,'frozen_inputs':8,'baseline':8833,'assignment':50,'all_reservations_pairwise_disjoint':True,'protected_and_coverage_disjoint':True,'binding_count':len(refs),'scientific_reading_started':False})
print('PASS prereading',len(refs))
