import json,hashlib,pathlib,datetime
R=pathlib.Path(__file__).resolve().parent; L=R.parent; ROOT=L.parents[4]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def put(n,j):(R/n).write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
def load(p):return json.loads(p.read_text())
bound={}
def bind(p):
 p=p.resolve();bound[str(p)]={'original':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
 return p
def check(p,e):
 assert p.is_file(),str(p)
 assert sha(p)==e['sha256'],str(p)
 size=e.get('bytes',e.get('size'))
 if size is not None: assert p.stat().st_size==size,str(p)
def validate(n):
 d=L/n;m=bind(d/'manifest.json');j=load(m);es=j if isinstance(j,list) else j['files']+j.get('frozen_inputs',[])
 names=[e['path'] for e in es];assert len(names)==len(set(names))
 actual={str(p.relative_to(d)) for p in d.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}
 assert actual==set(names),(n,actual-set(names),set(names)-actual)
 for e in es:check(d/e['path'],e)
 return {'lane':n,'entries':len(es),'exact_set':True,'all_hashes_and_declared_sizes':True}
reports=[validate(n) for n in ['root-mathdb-breadth-intake-r445','pi-mathdb-full-corpus-inventory-r301','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']]
I=L/'root-mathdb-breadth-intake-r445'
for x in load(I/'bindings.json'):
 p=bind(pathlib.Path(x['original']));check(p,x)
for n in ['reserved-ids.json','queue.json','coverage-delta.json','bindings.json']:bind(I/n)
C=L/'pi-mathdb-full-corpus-inventory-r301'
chunks=sorted((C/'corpus').glob('*.jsonl'));assert len(chunks)==20
for p in chunks:bind(p)
for n in ['accepted-exclusions.json','historical-dispositions.json']:bind(L/'root-mathdb-accepted-exclusions-r304'/n)
for n in ['disposition.json','DECISION.md']:bind(L/'root-mathdb-cayley-review-intake-r363'/n)
for p in [ROOT/'AGENTS.md',L.parent/'AGENTS.md',L.parent/'ledger.json',L.parent/'prior-campaign-context.json',ROOT/'sources/upstream.json',ROOT/'sources/CONTENTS.md',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:
 if p.is_file():bind(p)
put('bindings.json',list(bound.values()));put('freeze-receipt.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','manifest_validation':reports,'originals':len(bound),'chunks':20,'upstream_code_executed':False})
print('PASS freeze',len(bound),'originals',reports)
