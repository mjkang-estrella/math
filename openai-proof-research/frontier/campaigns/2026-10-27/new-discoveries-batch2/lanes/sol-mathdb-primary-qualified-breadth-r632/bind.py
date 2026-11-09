from pathlib import Path
import json,hashlib
O=Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r631';R=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def bind(p):
 d=p.read_bytes();return {'path':str(p),'size':len(d),'sha256':hashlib.sha256(d).hexdigest()}
def check(p,e):
 b=bind(p);assert b['size']==e.get('size',e.get('bytes')),str(p);assert b['sha256']==e['sha256'],str(p);return b
out=[]
for e in j(O/'initial-bindings.json'):out.append(check(Path(e['path']),e))
m=j(I/'manifest.json');expected={e['path'] for e in m['files']};assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}==expected|{'manifest.json','verification-receipt.json'}
for e in m['files']:check(I/e['path'],e)
for e in j(I/'bindings.json'):
 for k in ['original','copy']:out.append(check(Path(e[k]),e))
m=j(R/'manifest.json');chunks=[e for e in m['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(m['frozen_inputs'])==8
for e in chunks+m['frozen_inputs']:out.append(check(R/e['path'],e))
for e in j(L/'sol-mathdb-primary-qualified-breadth-r626/flat-bindings.json'):out.append(check(Path(e['path']),e))
for p in [L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md',I.parent.parent/'ledger.json',I.parent.parent/'prior-campaign-context.json']:
 out.append(bind(p))
(O/'flat-bindings.json').write_text(json.dumps(list({e['path']:e for e in out}.values()),indent=2)+'\n')
c=j(I/'coverage-delta.json');assert len(c)==6683
sets=[set(a['ids']) for a in j(I/'active-breadth-reservations.json')];assert len(sets)==3
for n,s in enumerate(sets):
 assert len(s)==50 and not s&set(map(int,c))
 for t in sets[:n]:assert not s&t
q=j(I/'queue-r632.json');ids=set(j(I/'reserved-ids-r632.json')['ids']);assert ids==sets[2]=={a['mathdb_id'] for a in q};assert not ids&set(j(I/'reserved-ids-r632.json')['protected_ids'])
rows=[]
for e in chunks:
 p=R/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r.get('mathdb_id') in ids:
   rows.append({'mathdb_id':r['mathdb_id'],'chunk':str(p),'line':n,'record':r,'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(rows)==50
(O/'literal-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
(O/'binding-receipt.json').write_text(json.dumps({'status':'PASS','chunks':20,'frozen_inputs':8,'coverage_baseline':6683,'assigned_records':50,'all_reservations_pairwise_disjoint':True,'flat_bindings':len(set(e['path'] for e in out))},indent=2)+'\n')
for x in rows:print(json.dumps(x['record'],ensure_ascii=False))
