"""Independent read-only verifier. Run under the fixed helper guard. No upstream code execution."""
import pathlib,json,hashlib,sys,datetime,tempfile
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r535';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes()
 if len(b)!=e.get('size',e.get('bytes')):raise ValueError('size mismatch '+str(p))
 if h(b)!=e['sha256']:raise ValueError('hash mismatch '+str(p))
def exact(root,m):
 names=[e['path'] for e in m['files']]
 if len(names)!=len(set(names)):raise ValueError('duplicate payload path')
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
 if actual-set(m['excluded_exact_paths'])!=set(names):raise ValueError('extra/missing payload')
 for e in m['files']:check(root/e['path'],e)
def negatives():
 result=[]
 with tempfile.TemporaryDirectory(prefix='negative-',dir=P) as td:
  root=pathlib.Path(td);p=root/'sample';p.write_bytes(b'abcd');e={'path':'sample','size':4,'sha256':h(b'abcd')};m={'files':[e],'excluded_exact_paths':[]};exact(root,m)
  for name,change in [('hash',{'sha256':'0'*64}),('size',{'size':5})]:
   try:check(p,dict(e,**change))
   except ValueError:result.append(name+'_rejected')
   else:raise ValueError('negative accepted')
  (root/'extra').write_bytes(b'x')
  try:exact(root,m)
  except ValueError:result.append('extra_file_rejected')
  else:raise ValueError('extra negative accepted')
 return result
if '--negative-tests' in sys.argv:print(json.dumps({'tests':negatives(),'originals_mutated':False}));sys.exit(0)
# Initial hash list anchors the intake manifest/queue/reservations/receipt before content read.
for line in (P/'initial-sha256.txt').read_text().splitlines():
 sha,name=line.split(None,1);p=pathlib.Path(name.strip());assert h(p.read_bytes())==sha,str(p)
for e in j(P/'flat-bindings.json'):check(pathlib.Path(e['path']),e)
# Intake exact payload and direct pair checking; do not execute its verify.py.
exact(I,j(I/'manifest.json'))
for e in j(I/'bindings.json'):
 for k in ['original','copy']:check(pathlib.Path(e[k]),e)
cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')]
assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
cov=j(I/'coverage-delta.json');assert len(cov)==4333
seen=set();active=j(I/'active-breadth-reservations.json')
for r in active:
 ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
res=j(I/'reserved-ids.json');assert res['lane']==P.name
ids=set(res['ids']);assert len(ids)==50 and ids=={r['mathdb_id'] for r in j(I/'queue.json')}
found={}
for e in chunks:
 p=C/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(p,n,r)
assert set(found)==ids
ds=j(P/'dispositions.json');assert len(ds)==50 and {d['mathdb_id'] for d in ds}==ids
for d in ds:
 p,n,r=found[d['mathdb_id']]
 assert d['corpus_chunk']==str(p) and d['corpus_line_1based']==n and d['statement']==r['statement']
 assert d['statement_utf8_sha256']==h(r['statement'].encode())
 assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
 assert d['credit']==0 and d['literal_statement_reviewed'] and not d['novelty_pass'] and not d['current_registry_cleared']
assert j(P/'proposals.json')==[]
for name in ['download-bindings.json','derivative-bindings.json']:
 for e in j(P/name):
  if 'path' in e:check(P/e['path'],e)
exact(P,j(P/'manifest.json'))
b=(P/'manifest.json').read_bytes()
print(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'integrity':'PASS','manifest_sha256':h(b),'manifest_size':len(b),'payload_files':len(j(P/'manifest.json')['files']),'flat_bindings':len(j(P/'flat-bindings.json')),'original_chunks':20,'frozen_inputs':8,'baseline_literal_reviews':4333,'new_literal_reviews':50,'proposals':0,'reservation_disjointness':True,'negative_tests':j(P/'negative-test-results.json'),'scientific_acceptance':False,'novelty':'HOLD','credit':0},indent=2))
