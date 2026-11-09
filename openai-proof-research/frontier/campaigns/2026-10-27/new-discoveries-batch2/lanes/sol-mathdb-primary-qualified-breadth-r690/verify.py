"""Independent read-only verifier. No imported upstream scripts, writes or network."""
import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r689';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'size mismatch: {p}';assert h(b)==e['sha256'],f'hash mismatch: {p}'
def exact(root,m,extra=None):
 names={e['path'] for e in m['files']};assert len(names)==len(m['files']),'duplicate manifest path'
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
 if extra:actual.add(extra)
 assert actual-set(m['excluded_exact_paths'])==names,'extra or missing payload'
 for e in m['files']:check(root/e['path'],e)
def validate():
 m=j(P/'manifest.json');assert set(m['excluded_exact_paths'])=={'manifest.json','final-verification-receipt.json'}
 if '--negative-hash' in sys.argv:m['files'][0]['sha256']='0'*64
 if '--negative-size' in sys.argv:m['files'][0]['size']+=1
 exact(P,m,'INJECTED-extra-file' if '--negative-extra' in sys.argv else None)
 refs=j(P/'flat-bindings.json');bound={e['path']:e for e in refs}
 for e in refs:check(pathlib.Path(e['path']),e)
 for name in ['manifest.json','verification-receipt.json','queue-r690.json','reserved-ids-r690.json','coverage-delta.json','adjudications.json','hypothesis-queue.json','bindings.json']:
  assert str(I/name) in bound
 exact(I,j(I/'manifest.json'))
 pairs=j(I/'bindings.json');assert len(pairs)==49
 for e in pairs:
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 cm=j(C/'manifest.json');assert str(C/'manifest.json') in bound
 chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==8133
 active=j(I/'active-breadth-reservations.json');assert len(active)==3;seen=set()
 for a in active:
  ids=set(a['ids']);assert len(ids)==len(a['ids'])==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(a['protected_ids']);seen|=ids
 assert len(seen)==150
 assert next(a for a in active if a['lane'].endswith('r628'))['status']=='rate_limit_held_not_reconciled'
 assert any(a['lane'].endswith('r688') for a in active)
 q=j(I/'queue-r690.json');res=j(I/'reserved-ids-r690.json');ids=set(res['ids']);assert len(q)==len(ids)==50 and ids=={r['mathdb_id'] for r in q}
 ds=j(P/'dispositions.json');assert len(ds)==50 and {d['mathdb_id'] for d in ds}==ids
 lits=j(P/'literal-records.json');assert len(lits)==50 and {x['record']['mathdb_id'] for x in lits}==ids
 # Locate assigned originals without displaying adjacent/unassigned content.
 found={}
 for e in chunks:
  for n,line in enumerate((C/e['path']).open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:
    assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(e['path'],n,r)
 assert len(found)==50
 for x in lits:
  ck,n,r=found[x['record']['mathdb_id']];assert (x['chunk'],x['line'],x['record'])==(ck,n,r)
 for d in ds:
  ck,n,r=found[d['mathdb_id']];assert (d['chunk'],d['line'],d['statement_utf8'])==(ck,n,r['statement'])
  assert d['statement_sha256']==h(r['statement'].encode()) and d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  assert d['classification'] in {'complete','definition-dependent','scope-ambiguous','incomplete'} and d['classification_reason_and_quantifiers'] and d['technical_assessment']
  assert d['accepted_credit']==0 and d['current_registry_cleared'] is False
 assert j(P/'proposals.json')==[]
 for e in j(P/'source-provenance.json'):
  if 'path' in e:check(P/e['path'],e)
 for line in (P/'derivative-bindings.jsonl').read_text().splitlines():
  e=json.loads(line);check(P/e['path'],e)
 initial=j(P/'initial-checks.json');assert initial['original_chunks']==20 and initial['frozen_inputs']==8
 return {'integrity':'PASS','intake_exact':True,'original_chunks':20,'frozen_inputs':8,'original_copy_pairs':49,'literal_reviews':50,'reserved_disjoint_ids':150,'baseline':8133,'proposals':0,'scientific_acceptance':False,'novelty':'HOLD'}
if __name__=='__main__':
 try:print(json.dumps(validate(),sort_keys=True))
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
