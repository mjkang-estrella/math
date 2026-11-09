import pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r563';C=L/'pi-mathdb-full-corpus-inventory-r301';B=L.parent
refs={}
def bind(p):
 p=p.resolve();b=p.read_bytes();e={'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()};refs[str(p)]=e;return b
def j(p):return json.loads(bind(p))
def check(p,e):
 b=bind(p);assert len(b)==e.get('size',e.get('bytes')) and hashlib.sha256(b).hexdigest()==e['sha256'],str(p)
m=j(I/'manifest.json');actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()};assert actual-set(m['excluded_exact_paths'])=={e['path'] for e in m['files']}
for e in m['files']:check(I/e['path'],e)
bind(I/'verification-receipt.json')
for e in j(I/'bindings.json'):
 for k in ['original','copy']:check(pathlib.Path(e[k]),e)
cm=j(C/'manifest.json');assert bind(C/'manifest.json')==bind(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json')
chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-breadth-reconciliation-r304/accepted-exclusions.json',L/'root-mathdb-breadth-reconciliation-r304/historical-dispositions.json']:
 if p.exists():bind(p)
# Locate required flat adjudication paths without reading their content.
for p in L.glob('*r304/*.json'):
 if p.name in ['accepted-exclusions.json','historical-dispositions.json']:bind(p)
for p in L.glob('*r363/*'):
 if p.is_file():bind(p)
res=j(I/'reserved-ids.json');q=j(I/'queue.json');cov=j(I/'coverage-delta.json');active=j(I/'active-breadth-reservations.json');assert len(cov)==5033
seen=set()
for r in active:
 ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
assert len(seen)==150 and res['lane']==P.name and set(res['ids'])=={r['mathdb_id'] for r in q} and len(q)==50
(P/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
(P/'binding-receipt.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'intake_exact':True,'direct_pairs':len(j(I/'bindings.json')),'chunks':20,'frozen_inputs':8,'coverage':5033,'disjoint_reserved':150},indent=2)+'\n')
print('BOUND',len(refs));print(json.dumps(q,ensure_ascii=False,indent=2))
