from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parent; L=D.parent; B=L.parent
out={}
def bind(p,expected=None):
 p=Path(p); b=p.read_bytes(); r={'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
 if expected: assert r['size']==expected['size'] and r['sha256']==expected['sha256'],str(p)
 out[str(p)]=r
 return r
def load(p):return json.loads(Path(p).read_text())
for n in ['root-mathdb-breadth-intake-r577','root-mathdb-breadth-intake-r579']:
 d=L/n
 for p in d.glob('*.json'):bind(p)
 m=load(d/'manifest.json'); expected={x['path'] for x in m['files']}
 actual={str(p.relative_to(d)) for p in d.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])
 assert actual==expected,(n,actual^expected)
 for r in m['files']:bind(d/r['path'],r)
 for r in load(d/'bindings.json'):
  bind(r['original'],r);bind(r['copy'],r)
inv=L/'pi-mathdb-full-corpus-inventory-r301/manifest.json'
m=load(inv)
print('inventory keys',m.keys())
print(json.dumps(m,ensure_ascii=False)[:3800])
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-breadth-intake-r304/accepted-exclusions.json',L/'root-mathdb-breadth-intake-r304/historical-dispositions.json']:
 if p.exists():bind(p)
(D/'flat-bindings.json').write_text(json.dumps(list(out.values()),indent=2)+'\n')
chunks=[r for r in m['files'] if r['path'].startswith('corpus/')]
assert len(chunks)==20 and len(m['frozen_inputs'])==8
for r in chunks+m['frozen_inputs']:bind(inv.parent/r['path'],{'size':r['bytes'],'sha256':r['sha256']})
for p in [L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md']:bind(p)
(D/'flat-bindings.json').write_text(json.dumps(list(out.values()),indent=2)+'\n')
ids=load(L/'root-mathdb-breadth-intake-r577/reserved-ids.json')['ids']; assert len(ids)==len(set(ids))==50
q=load(L/'root-mathdb-breadth-intake-r577/queue.json');assert set(ids)=={r['mathdb_id'] for r in q}
cov=load(L/'root-mathdb-breadth-intake-r579/coverage-delta.json');assert len(cov)==5433
res=load(L/'root-mathdb-breadth-intake-r579/active-breadth-reservations.json');seen=set()
for r in res:
 s=set(r['ids']);assert len(s)==50 and not(s&seen) and not(s&set(map(int,cov))) and not(s&set(r['protected_ids']));seen|=s
assert next(r['ids'] for r in res if r['lane']==D.name)==ids
rows=[]
for c in chunks:
 p=inv.parent/c['path']
 for no,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   st=r['statement'];rows.append({'mathdb_id':r['mathdb_id'],'chunk':str(p),'line':no,'statement':st,'statement_sha256':hashlib.sha256(st.encode()).hexdigest(),'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'record':r})
assert len(rows)==50
rows.sort(key=lambda r:ids.index(r['mathdb_id']))
(D/'literal-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
(D/'binding-receipt.json').write_text(json.dumps({'intake_payloads':'PASS independent hash/size/exact-file/pair checks','original_chunks_verified':20,'separate_frozen_inputs_verified':8,'assigned_count':50,'baseline':5383,'latest_baseline':5433,'all_active_reservations_disjoint':True},indent=2)+'\n')
for r in rows:print('\nID',r['mathdb_id'],r['record']['title'],'\n',r['statement'],'\nSOURCE',r['record']['source_url'],r['record']['references'])
