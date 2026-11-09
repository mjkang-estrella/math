"""Independent read-only verifier. Run under the fixed helper guard. No writes."""
import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r519';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes()
 if len(b)!=e.get('size',e.get('bytes')):raise ValueError('SIZE '+str(p))
 if h(b)!=e['sha256']:raise ValueError('HASH '+str(p))
def exact(root,m):
 if m['excluded_exact_paths']!=['manifest.json','final-verification-receipt.json']:raise ValueError('exclusions')
 files=m['files'];names={e['path'] for e in files}
 if len(names)!=len(files):raise ValueError('duplicate payload name')
 if any(pathlib.Path(n).is_absolute() or '..' in pathlib.Path(n).parts for n in names):raise ValueError('unsafe payload name')
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
 if actual-set(m['excluded_exact_paths'])!=names:raise ValueError('EXTRA_OR_MISSING_FILE')
 for e in files:check(root/e['path'],e)
def validate():
 exact(P,j(P/'manifest.json'))
 for path,e in j(P/'flat-bindings.json').items():check(pathlib.Path(path),e)
 m=j(I/'manifest.json');names={e['path'] for e in m['files']}
 assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])==names
 for e in m['files']:check(I/e['path'],e)
 pairs=j(I/'bindings.json');assert len(pairs)==79
 for e in pairs:
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==4083
 active=j(I/'active-breadth-reservations.json');assert len(active)==3;seen=set()
 for r in active:
  ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
 for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
 assert next(r for r in active if 'r504' in r['lane'])['status']=='rate_limited_reserved_unreviewed'
 q=j(I/'queue-r520.json');ids={r['mathdb_id'] for r in q};assert len(q)==len(ids)==50 and ids==set(j(I/'reserved-ids-r520.json')['ids'])
 route=[json.loads(line) for line in (I/'routing-queue.jsonl').open()];assert len(route)==6000 and all(r in route for r in q)
 assert (I/'routing-queue.jsonl').read_bytes()==(I/'frozen/root-mathdb-breadth-intake-r517/routing-queue.jsonl').read_bytes()
 found={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(str(p),n,r)
 ds=j(P/'dispositions.json');assert len(ds)==50 and {d['mathdb_id'] for d in ds}==ids and len(found)==50
 assigned=j(P/'assigned-records.json');assert len(assigned)==50
 for d in ds+assigned:
  p,n,r=found[d['mathdb_id']];assert d['corpus_chunk']==p and d['corpus_line']==n and d['statement']==r['statement']
  assert d['statement_utf8_sha256']==h(r['statement'].encode())
  assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  if 'record' in d:assert d['record']==r
 notes={int(a):(b,c) for a,b,c in (s.rstrip('\n').split('\t',2) for s in (P/'notes.tsv').open())};assert set(notes)==ids
 for d in ds:
  assert (d['disposition'],d['technical_disposition'])==notes[d['mathdb_id']]
  assert d['literal_full_statement_read'] and d['accepted_credit']==0 and not d['current_registry_cleared'] and not d['full_dependency_audit']
 assert j(P/'proposals.json')==[]
 for filename in ['source-bindings.json','derivative-bindings.json']:
  for e in j(P/filename):
   if 'path' in e:check(pathlib.Path(e['path']),e)
 neg=j(P/'negative-tests.json');assert len(neg)==3 and all(t['returncode']!=0 and t['expected_error'] in t['output'] for t in neg)
 return {'integrity':'PASS','original_copy_pairs':79,'original_chunks':20,'frozen_inputs':8,'baseline_literal_reviews':4083,'routing_metadata_rows':6000,'assigned_literal_reviews':50,'reserved_sets_disjoint':True,'proposals':0,'scientific_acceptance':False,'novelty':'HOLD','manifest':{'size':(P/'manifest.json').stat().st_size,'sha256':h((P/'manifest.json').read_bytes())}}
try:
 if '--payload-root' in sys.argv:
  root=pathlib.Path(sys.argv[sys.argv.index('--payload-root')+1]);exact(root,j(root/'manifest.json'));print('fixture PASS')
 else:print(json.dumps(validate(),sort_keys=True))
except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
