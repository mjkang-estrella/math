"""Read-only verifier. Run through verify.sh (fixed resource guard)."""
import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r659';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(d):return hashlib.sha256(d).hexdigest()
def check(p,e):
 d=p.read_bytes();assert len(d)==e.get('size',e.get('bytes')),f'size: {p}';assert h(d)==e['sha256'],f'hash: {p}'
def exact(root,m):
 names=[e['path'] for e in m['files']];assert len(names)==len(set(names));assert set(m['excluded_exact_paths'])=={'manifest.json','final-verification-receipt.json'} if root==P else True
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()};assert actual-set(m['excluded_exact_paths'])==set(names),'extra/missing payload'
 for e in m['files']:check(root/e['path'],e)
def verify():
 for e in j(P/'initial-bindings.json'):check(pathlib.Path(e['path']),e)
 im=j(I/'manifest.json');exact(I,im)
 for e in j(I/'bindings.json'):
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 for p,e in j(P/'flat-bindings.json').items():check(pathlib.Path(p),e)
 cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==7383
 active=j(I/'active-breadth-reservations.json');seen=set();protected=set(j(I/'reserved-ids-r660.json')['protected_ids'])
 for r in active:
  ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&protected;seen|=ids
 for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
 ids=set(j(I/'reserved-ids-r660.json')['ids']);assert ids=={r['mathdb_id'] for r in j(I/'queue-r660.json')}
 found={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(str(p),n,r)
 ds=j(P/'dispositions.json');assert len(ds)==50 and {d['mathdb_id'] for d in ds}==ids
 for d in ds:
  p,n,r=found[d['mathdb_id']];assert (d['corpus_chunk'],d['corpus_line'])==(p,n);assert d['statement']==r['statement'];assert d['statement_utf8_sha256']==h(r['statement'].encode());assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode());assert d['independent_completeness'] in ['complete','definition-dependent','scope-ambiguous','incomplete'];assert d['completeness_reason'] and d['quantifier_and_technical_assessment'];assert d['accepted_credit']==0 and not d['current_registry_cleared']
 for x in j(P/'literal-records.json'):
  p,n,r=found[x['record']['mathdb_id']];assert x==dict(corpus_chunk=p,corpus_line=n,record=r)
 assert len(j(P/'proposals.json'))<=3
 for e in j(P/'source-provenance.json'):
  if 'sha256' in e:check(P/e['path'],e)
 for e in j(P/'derivative-bindings.json'):check(P/e['path'],e)
 exact(P,j(P/'manifest.json'))
 print(json.dumps(dict(integrity='PASS',literal_reviews=50,baseline=7383,original_chunks=20,frozen_inputs=8,original_copy_pairs=len(j(I/'bindings.json')),disjoint_reservations=3,proposals=len(j(P/'proposals.json')),mathematical_acceptance=False)))
if __name__=='__main__':
 try:verify()
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
