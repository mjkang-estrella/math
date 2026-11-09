"""Independent read-only verifier. Invoke using the fixed helper_guard.py."""
import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r723';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes()
 if len(b)!=e.get('size',e.get('bytes')):raise ValueError('size mismatch: '+str(p))
 if h(b)!=e['sha256']:raise ValueError('hash mismatch: '+str(p))
def exact(root,m):
 excluded=m['excluded_exact_paths'];names=[e['path'] for e in m['files']]
 if len(names)!=len(set(names)):raise ValueError('duplicate manifest path')
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(excluded)
 if actual!=set(names):raise ValueError('extra/missing payload: '+str(actual^set(names)))
 for e in m['files']:
  if pathlib.Path(e['path']).is_absolute() or '..' in pathlib.Path(e['path']).parts:raise ValueError('unsafe relative path')
  check(root/e['path'],e)
def verify():
 m=j(P/'manifest.json');assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json'];exact(P,m)
 refs=j(P/'flat-bindings.json');assert len(refs)==len({e['path'] for e in refs})
 for e in refs:check(pathlib.Path(e['path']),e)
 check(I/'manifest.json',{'size':11091,'sha256':'31e61bcb13bcc169300bd6e8da4ed60363b921da9b2cfbb51fad364c23e9ae4b'})
 exact(I,j(I/'manifest.json'))
 pairs=j(I/'bindings.json');assert len(pairs)==47
 for e in pairs:
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 cm=j(C/'manifest.json');check(C/'manifest.json',{'size':22047,'sha256':'4da10b6dcd6d56a34399195f26abe9ff13f8c3fd67e88b672fc35db2a2a71e15'})
 chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 # Actual r304 originals must also equal their r301 frozen copies.
 for n in ['accepted-exclusions.json','historical-dispositions.json']:
  assert (L/'root-mathdb-accepted-exclusions-r304'/n).read_bytes()==(C/'frozen/root-mathdb-accepted-exclusions-r304'/n).read_bytes()
 cov=j(I/'coverage-delta.json');assert len(cov)==8983
 active=j(I/'active-breadth-reservations.json');assert len(active)==3;seen=set()
 for a in active:
  ids=set(a['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(a['protected_ids']);seen|=ids
 assert len(seen)==150
 for a in active:assert set(a['other_active_reservations'])==seen-set(a['ids'])
 q=j(I/'queue-r724.json');res=j(I/'reserved-ids-r724.json');ids={r['mathdb_id'] for r in q};assert ids==set(res['ids']) and len(q)==50 and res['lane']==P.name
 assert next(a for a in active if a['lane']==P.name)['ids']==res['ids']
 rows=j(P/'dispositions.json');ls=j(P/'literal-records.json');assert len(rows)==len(ls)==50 and {d['mathdb_id'] for d in rows}==ids and len({d['mathdb_id'] for d in rows})==50
 found={}
 for e in chunks:
  for n,l in enumerate((C/e['path']).open(),1):
   r=json.loads(l)
   if r['mathdb_id'] in ids:
    assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(e['path'],n,r)
 assert len(found)==50
 for d in rows:
  ck,n,r=found[d['mathdb_id']];lit=next(x for x in ls if x['mathdb_id']==d['mathdb_id'])
  assert (d['corpus_chunk'],d['corpus_line'])==(ck,n)==(lit['corpus_chunk'],lit['corpus_line']) and r==lit['record']
  assert d['exact_utf8_statement']==r['statement'] and d['statement_utf8_sha256']==lit['statement_utf8_sha256']==h(r['statement'].encode('utf8'))
  assert d['canonical_record_sha256']==lit['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf8'))
  assert d['classification'] in {'complete','definition-dependent','scope-ambiguous','incomplete'} and d['classification_reason'] and d['quantifier_scope'] and d['technical_assessment']
  assert d['accepted_credit']==0 and d['current_registry_cleared'] is False and d['proposal'] is False
 assert j(P/'proposals.json')==[]
 for s in j(P/'source-provenance.json'):
  for kind in ['pdf','text']:check(P/s[kind+'_path'],{'size':s[kind+'_size'],'sha256':s[kind+'_sha256']})
 return {'integrity':'PASS','literal_records':50,'baseline':8983,'baseline_relative_union':9033,'chunks_in_place':20,'frozen_inputs':8,'direct_original_copy_pairs':47,'flat_bindings':len(refs),'reservation_sets':3,'proposals':0,'credit':0,'math_and_novelty':'NOT_CERTIFIED; registry HOLD'}
if __name__=='__main__':
 try:print(json.dumps(verify(),sort_keys=True))
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
