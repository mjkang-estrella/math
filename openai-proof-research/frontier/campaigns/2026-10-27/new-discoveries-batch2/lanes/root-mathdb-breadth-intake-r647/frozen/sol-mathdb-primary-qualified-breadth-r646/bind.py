import pathlib,json,hashlib
O=pathlib.Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r643';R=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def info(p):
 b=p.read_bytes();return {'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def check(p,e):assert info(p)=={'sha256':e['sha256'],'size':e.get('size',e.get('bytes'))},str(p)
flat=load(O/'initial-bindings.json')
for p,e in flat.items():check(pathlib.Path(p),e)
m=load(I/'manifest.json');expected={x['path'] for x in m['files']};actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths']);assert actual==expected
for e in m['files']:check(I/e['path'],e)
for e in load(I/'bindings.json'):
 for k in ['original','copy']:
  p=pathlib.Path(e[k]);check(p,e);flat[str(p)]=info(p)
assert str(R/'manifest.json') in flat
r=load(R/'manifest.json');chunks=[e for e in r['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20;assert len(r['frozen_inputs'])==8
for e in chunks+r['frozen_inputs']:
 p=R/e['path'];check(p,e);flat[str(p)]=info(p)
# Bind contextual originals before reading.
context=[L.parent/'ledger.json',L.parent/'prior-campaign-context.json']
context+=list((L/'root-mathdb-accepted-exclusions-r304').glob('*.json'))
context+=list(L.glob('*r363/*DECISION*'))+list(L.glob('*r363/*decision*'))
for p in context:flat[str(p)]=info(p)
(O/'flat-bindings.json').write_text(json.dumps(flat,indent=2)+'\n')
q=load(I/'queue-r646.json');ids={x['mathdb_id'] for x in q};res=load(I/'reserved-ids-r646.json');assert len(ids)==50 and ids==set(res['ids'])
cov=load(I/'coverage-delta.json');assert len(cov)==7033
sets=[set(x['ids']) for x in load(I/'active-breadth-reservations.json')];assert len(sets)==3
for j,s in enumerate(sets):
 assert not s&set(map(int,cov)) and not s&set(res['protected_ids'])
 for t in sets[:j]:assert not s&t
records=[]
for e in chunks:
 p=R/e['path']
 for n,line in enumerate(p.open(),1):
  # Decode records only if the serialized id belongs to this lane.
  import re
  match=re.search(r'"(?:mathdb_id|id)"\s*:\s*(\d+)',line)
  if match and int(match[1]) in ids:
   x=json.loads(line);records.append({'record':x,'chunk':str(p),'line':n,'canonical_record_sha256':hashlib.sha256(json.dumps(x,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(records)==50,len(records)
(O/'literal-records.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n')
(O/'binding-check.json').write_text(json.dumps({'intake_exact_payload':True,'original_copy_pairs':len(load(I/'bindings.json')),'chunks_in_place':20,'frozen_inputs':8,'baseline':7033,'reservations_disjoint':True,'context_bound':[str(x) for x in context]},indent=2)+'\n')
print('PASS',len(flat),'flat references; records',len(records));print('record keys',records[0]['record'].keys());print('context',[str(x) for x in context])
