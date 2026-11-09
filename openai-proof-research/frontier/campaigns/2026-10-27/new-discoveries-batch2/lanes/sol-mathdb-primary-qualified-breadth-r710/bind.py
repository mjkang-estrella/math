from pathlib import Path
import json,hashlib,datetime
P=Path(__file__).resolve().parent; L=P.parent; B=L.parent; I=L/'root-mathdb-breadth-intake-r709'; C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def digest(p):return {'path':str(p),'size':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def check(p,h,n):
 d=digest(p);assert d['size']==n and d['sha256']==h,str(p);return d
out=[]
for p in sorted(I.rglob('*')):
 if p.is_file():out.append(digest(p))
m=j(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={r['path'] for r in m['files']}|set(m['excluded_exact_paths'])
for r in m['files']:check(I/r['path'],r['sha256'],r['size'])
for r in j(I/'bindings.json'):
 for key in ['original','copy']:out.append(check(Path(r[key]),r['sha256'],r['bytes']))
cm=j(C/'manifest.json')
chunks=[r for r in cm['files'] if r['path'].startswith('corpus/')]
assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for r in chunks+cm['frozen_inputs']:out.append(check(C/r['path'],r['sha256'],r['bytes']))
for rel in ['ledger.json','prior-campaign-context.json']:
 out.append(digest(B/rel))
for lane,files in [('root-mathdb-accepted-exclusions-r304',['accepted-exclusions.json','historical-dispositions.json']),('root-mathdb-cayley-review-intake-r363',['DECISION.md','disposition.json'])]:
 for f in files:out.append(digest(L/lane/f))
cov=j(I/'coverage-delta.json');assert len(cov)==8633
active=j(I/'active-breadth-reservations.json');seen=set()
for r in active:
 ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
q=j(I/'queue-r710.json');res=j(I/'reserved-ids-r710.json')
assert len(q)==50 and {r['mathdb_id'] for r in q}==set(res['ids'])
(P/'flat-bindings.json').write_text(json.dumps(list({r['path']:r for r in out}.values()),indent=2)+'\n')
(P/'pre-reading-checks.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'integrity':'PASS','chunks':20,'frozen_inputs':8,'coverage':8633,'reservation_sets':len(active),'assignment':50,'disjoint':True,'upstream_verifier_executed':False,'deviation':'Before binding, diagnostic heads displayed coverage/admin and routing metadata, not scientific statements; scientific reading starts after this receipt.'},indent=2)+'\n')
print('PASS all pre-reading checks')
