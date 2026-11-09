import pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r727';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def ent(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def chk(p,e):
 a=ent(p);assert a['sha256']==e['sha256'] and a['size']==e.get('size',e.get('bytes')),str(p)
refs={}
def bind(p):refs[str(p)]=ent(p)
bind(I/'manifest.json');bind(I/'verification-receipt.json')
m=j(I/'manifest.json');names={e['path'] for e in m['files']}
assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])==names
for e in m['files']:chk(I/e['path'],e);bind(I/e['path'])
for e in j(I/'bindings.json'):
 for key in ['original','copy']:chk(pathlib.Path(e[key]),e);bind(pathlib.Path(e[key]))
cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')]
assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:chk(C/e['path'],e);bind(C/e['path'])
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']+list((L/'root-mathdb-cayley-review-intake-r363').glob('*.md')):bind(p)
(P/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
cov=j(I/'coverage-delta.json');assert len(cov)==9083
active=j(I/'active-breadth-reservations.json');seen=set()
for r in active:
 ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
ids=set(j(I/'reserved-ids-r728.json')['ids']);assert ids=={r['mathdb_id'] for r in j(I/'queue-r728.json')}
found=[]
for e in chunks:
 p=C/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:found.append({'corpus_chunk':str(p),'corpus_line':n,'record':r,'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(found)==50
(P/'literal-records.json').write_text(json.dumps(found,ensure_ascii=False,indent=2)+'\n')
(P/'initial-checks.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'intake_exact':True,'direct_pairs':len(j(I/'bindings.json')),'chunks':20,'frozen_inputs':8,'baseline':9083,'disjoint':True,'bindings':len(refs)},indent=2)+'\n')
print('PASS',len(refs));print(json.dumps(found[0],ensure_ascii=False,indent=2))
