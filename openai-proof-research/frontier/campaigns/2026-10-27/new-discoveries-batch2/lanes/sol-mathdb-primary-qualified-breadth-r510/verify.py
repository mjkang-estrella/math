"""Independent read-only verifier. Run with fixed helper_guard.py; never runs upstream code."""
import pathlib,json,hashlib,sys,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r509';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def checkbytes(b,e):
 if len(b)!=e.get('size',e.get('bytes')):raise ValueError('size mismatch')
 if h(b)!=e['sha256']:raise ValueError('hash mismatch')
def check(p,e):
 try:checkbytes(p.read_bytes(),e)
 except Exception as err:raise ValueError(str(p)+': '+str(err)) from err
def fileset(actual,m):
 expected=[e['path'] for e in m['files']]
 if len(expected)!=len(set(expected)) or actual-set(m['excluded_exact_paths'])!=set(expected):raise ValueError('exact payload/extra-file mismatch')
def exact(root,m):
 fileset({str(q.relative_to(root)) for q in root.rglob('*') if q.is_file()},m)
 for e in m['files']:check(root/e['path'],e)
def negatives():
 # Pure bounded synthetic fixtures; same functions as real verifier, no originals modified.
 good={'size':1,'sha256':h(b'a')};out={}
 for name,b,e in [('hash',b'b',good),('size',b'aa',good)]:
  try:checkbytes(b,e)
  except ValueError:out[name+'_rejected']=True
  else:raise ValueError('negative accepted: '+name)
 try:fileset({'a','extra'},{'files':[{'path':'a'}],'excluded_exact_paths':[]})
 except ValueError:out['extra_file_rejected']=True
 else:raise ValueError('extra negative accepted')
 return out
if '--negative-tests' in sys.argv:print(json.dumps(negatives()));sys.exit(0)
if '--negative-case' in sys.argv:
 case=sys.argv[-1]
 if case=='hash':checkbytes(b'b',{'size':1,'sha256':h(b'a')})
 elif case=='size':checkbytes(b'aa',{'size':1,'sha256':h(b'a')})
 elif case=='extra':fileset({'a','extra'},{'files':[{'path':'a'}],'excluded_exact_paths':[]})
 else:raise ValueError('unknown negative case')
 raise RuntimeError('negative unexpectedly accepted')
for e in j(P/'flat-bindings.json'):check(pathlib.Path(e['path']),e)
exact(I,j(I/'manifest.json'))
for e in j(I/'bindings.json'):
 for k in ['original','copy']:check(pathlib.Path(e[k]),e)
cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')]
assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
cov=j(I/'coverage-delta.json');assert len(cov)==3783
res=j(I/'reserved-ids.json');assert res['lane']==P.name
ids=set(res['ids']);assert len(ids)==50 and ids=={r['mathdb_id'] for r in j(I/'queue.json')}
seen=set()
for r in j(I/'active-breadth-reservations.json'):
 s=set(r['ids']);assert len(s)==50 and not s&seen and not {str(x) for x in s}&set(cov) and not s&set(r['protected_ids']);seen|=s
assert len(seen)==150 and not ids&set(res['other_active_reservations']) and not ids&set(res['protected_ids'])
found={}
for e in chunks:
 p=C/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(p,n,r)
assert set(found)==ids
for name in ['assigned-records.json','dispositions.json']:
 rows=j(P/name);assert len(rows)==50 and {x['mathdb_id'] for x in rows}==ids
 for d in rows:
  p,n,r=found[d['mathdb_id']];assert d['corpus_chunk']==str(p) and d['corpus_line']==n and d['statement']==r['statement'];assert d['statement_utf8_sha256']==h(r['statement'].encode());assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  if 'record' in d:assert d['record']==r
  if name=='dispositions.json':assert d['accepted_credit']==0 and not d['current_registry_cleared'] and d['literal_statement_read']
assert j(P/'proposals.json')==[]
for name in ['source-bindings.json','derivative-bindings.json']:
 for e in j(P/name):
  if 'path' in e:check(pathlib.Path(e['path']),e)
m=j(P/'manifest.json');assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json'];exact(P,m)
mb=(P/'manifest.json').read_bytes()
if '--payload-only' not in sys.argv:
 receipt=j(P/'final-verification-receipt.json');assert receipt['manifest_sha256']==h(mb) and receipt['manifest_size']==len(mb) and receipt['integrity']=='PASS'
print(json.dumps({'integrity':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':h(mb),'manifest_size':len(mb),'payload_files':len(m['files']),'original_corpus_chunks':20,'original_frozen_inputs':8,'intake_exact':True,'original_copy_pairs':len(j(I/'bindings.json')),'literal_reviews':50,'coverage_baseline':3783,'reservation_sets_disjoint':True,'negative_tests':negatives(),'proposals':0,'scientific_acceptance':False,'current_registry_cleared':False}))
