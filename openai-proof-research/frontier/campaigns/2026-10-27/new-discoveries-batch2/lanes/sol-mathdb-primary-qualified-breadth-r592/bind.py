import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r591';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_bytes())
def entry(p):
 b=p.read_bytes();return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def check(p,e):
 a=entry(p);assert a['size']==e.get('size',e.get('bytes')) and a['sha256']==e['sha256'],str(p)
def exact(p,m):
 assert {str(x.relative_to(p)) for x in p.rglob('*') if x.is_file()}-set(m['excluded_exact_paths'])=={e['path'] for e in m['files']}
 for e in m['files']:check(p/e['path'],e)
for e in j(P/'initial-bindings.json'):check(pathlib.Path(e['path']),e)
exact(I,j(I/'manifest.json'))
refs={}
for e in j(I/'bindings.json'):
 for k in ['original','copy']:
  p=pathlib.Path(e[k]);check(p,e);refs[str(p)]=entry(p)
m=j(C/'manifest.json');chunks=[e for e in m['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(m['frozen_inputs'])==8
for e in chunks+m['frozen_inputs']:
 p=C/e['path'];check(p,e);refs[str(p)]=entry(p)
# Additional direct prior files are bound before content inspection, no recursive expansion.
for d,pat in [('root-mathdb-exclusions-r304','*.json'),('root-cayley-adjudication-r363','*')]:
 for p in (L/d).glob(pat):
  if p.is_file():refs[str(p)]=entry(p)
for p in L.glob('*r304/*'):
 if p.name in ['accepted-exclusions.json','historical-dispositions.json']:refs[str(p)]=entry(p)
for p in L.glob('*r363/*'):
 if p.is_file():refs[str(p)]=entry(p)
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'sol-mathdb-primary-qualified-breadth-r578/failures.json',L/'sol-mathdb-primary-qualified-breadth-r542/failures.json']:
 if p.exists():refs[str(p)]=entry(p)
(P/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
cov=j(I/'coverage-delta.json');assert len(cov)==5733
seen=set()
for r in j(I/'active-breadth-reservations.json'):
 ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
assert len(seen)==150
ids=set(j(I/'reserved-ids.json')['ids']);assert ids=={r['mathdb_id'] for r in j(I/'queue.json')}
records=[]
for e in chunks:
 p=C/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   records.append({'mathdb_id':r['mathdb_id'],'corpus_chunk':str(p),'corpus_line':n,'literal_statement':r['statement'],'statement_utf8_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'record':r})
assert len(records)==50
(P/'literal-records.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n')
print('BOUND: exact intake; all direct pairs; 20 original chunks + 8 frozen inputs; disjoint 150 reservations; 50 literal records')
print('prior paths',*[p for p in refs if any(t in p for t in ['r304','r363','failures','ledger','prior-campaign'])],sep='\n')
print('schema',records[0]['record'].keys())
