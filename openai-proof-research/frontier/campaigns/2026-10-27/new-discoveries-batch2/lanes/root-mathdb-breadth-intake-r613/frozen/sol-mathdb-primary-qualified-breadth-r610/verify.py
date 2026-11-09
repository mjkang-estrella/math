"""Independent read-only integrity verifier; never executes upstream scripts."""
import pathlib,json,hashlib,sys
D=pathlib.Path(__file__).resolve().parent;L=D.parent;I=L/'root-mathdb-breadth-intake-r609';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'size mismatch: {p}';assert h(b)==e['sha256'],f'hash mismatch: {p}'
def exact(root,m,negative=None):
 names=[x['path'] for x in m['files']];assert len(names)==len(set(names))
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])
 if negative=='extra':actual.add('SIMULATED_UNEXPECTED_FILE')
 assert actual==set(names),'extra/missing payload'
 for k,e in enumerate(m['files']):
  q=dict(e)
  if k==0 and negative=='hash':q['sha256']='0'*64
  if k==0 and negative=='size':q['size']+=1
  check(root/e['path'],q)
def validate(negative=None):
 m=j(D/'manifest.json');assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json'];exact(D,m,negative)
 for e in j(D/'flat-bindings.json'):check(pathlib.Path(e['path']),e)
 exact(I,j(I/'manifest.json'))
 pairs=j(I/'bindings.json')
 for e in pairs:
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 cm=j(C/'manifest.json');chunks=[x for x in cm['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==6183
 active=j(I/'active-breadth-reservations.json');assert len(active)==3;seen=set()
 for a in active:
  ids=set(a['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(a['protected_ids']);seen|=ids
 for a in active:assert set(a['other_active_reservations'])==seen-set(a['ids'])
 assigned=set(j(I/'reserved-ids-r610.json')['ids']);assert assigned=={x['mathdb_id'] for x in j(I/'queue-r610.json')}
 assert next(a for a in active if a['lane']==D.name)['ids']==j(I/'reserved-ids-r610.json')['ids']
 ds=j(D/'dispositions.json');assert len(ds)==50 and {x['mathdb_id'] for x in ds}==assigned;assert j(D/'proposals.json')==[]
 lits=j(D/'literal-records.json');assert len(lits)==50 and {x['record']['mathdb_id'] for x in lits}==assigned
 found={}
 for e in chunks:
  p=C/e['path']
  for n,l in enumerate(p.open(encoding='utf-8'),1):
   r=json.loads(l)
   if r['mathdb_id'] in assigned:assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(p,n,r)
 assert len(found)==50
 for d in ds:
  p,n,r=found[d['mathdb_id']];assert d['corpus_chunk']==str(p) and d['corpus_line']==n and d['statement']==r['statement'];assert d['statement_utf8_sha256']==h(r['statement'].encode('utf-8'));assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8'))
  lit=next(x for x in lits if x['record']['mathdb_id']==d['mathdb_id']);assert lit['record']==r
  for k in ['corpus_chunk','corpus_line','statement','statement_utf8_sha256','canonical_record_sha256']:assert lit[k]==d[k]
  assert d['accepted_credit']==0 and d['current_registry_cleared'] is False
  assert d['complete_mathematical_statement_review']==(d['literal_statement_scope']=='complete')
 for e in j(D/'source-provenance.json'):
  if 'path' in e:check(D/e['path'],e)
 for e in j(D/'derivative-bindings.json'):check(D/e['path'],e)
 checks=j(D/'bounded-checks.json');assert checks['executed'] and checks['literal_neighborhood_condition_pass'] is False
 return {'integrity':'PASS','literal_records':50,'complete_statement_reviews':sum(d['complete_mathematical_statement_review'] for d in ds),'incomplete_or_dependent_or_ambiguous':sum(not d['complete_mathematical_statement_review'] for d in ds),'proposals':0,'baseline_literal_reviews':6183,'intake_original_copy_pairs':len(pairs),'original_chunks':20,'frozen_inputs':8,'reservation_sets_disjoint':True,'math_or_novelty_acceptance':False,'manifest_sha256':h((D/'manifest.json').read_bytes()),'manifest_size':(D/'manifest.json').stat().st_size}
if __name__=='__main__':
 try:
  negative=sys.argv[2] if len(sys.argv)==3 and sys.argv[1]=='--negative' else None
  assert negative in [None,'hash','size','extra']
  print(json.dumps(validate(negative),sort_keys=True))
 except Exception as e:
  print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
