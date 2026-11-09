#!/usr/bin/env python3
"""Read-only verifier. Run via verify.sh; no upstream verifier imported or executed."""
import pathlib,json,hashlib,sys
D=pathlib.Path(__file__).resolve().parent;L=D.parent;I=L/'root-mathdb-breadth-intake-r721';R=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def digest(b):return hashlib.sha256(b).hexdigest()
def check(p,h,n):
 b=p.read_bytes();assert len(b)==n,('size',str(p));assert digest(b)==h,('hash',str(p))
def exact(root,m):
 expected={x['path'] for x in m['files']}|set(m['excluded_exact_paths'])
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
 assert actual==expected,('exact_payload',sorted(actual^expected))
 for x in m['files']:check(root/x['path'],x['sha256'],x['size'])
def main():
 m=load(D/'manifest.json')
 if len(sys.argv)>1:
  if sys.argv[1]=='--negative-hash':m['files'][0]['sha256']='0'*64
  elif sys.argv[1]=='--negative-size':m['files'][0]['size']+=1
  else:raise AssertionError('unknown test')
 exact(D,m)
 for x in load(D/'flat-bindings.json'):check(pathlib.Path(x['path']),x['sha256'],x['size'])
 assert digest((I/'manifest.json').read_bytes())=='110058e57a3257722135d46ba927836fce4ce435795d8ee4954901d7f68cf6eb'
 exact(I,load(I/'manifest.json'))
 pairs=load(I/'bindings.json')
 for x in pairs:
  check(pathlib.Path(x['original']),x['sha256'],x['bytes']);check(pathlib.Path(x['copy']),x['sha256'],x['bytes'])
 inv=load(R/'manifest.json');chunks=[x for x in inv['files'] if x['path'].startswith('corpus/')]
 assert len(chunks)==20 and len(inv['frozen_inputs'])==8
 for x in chunks+inv['frozen_inputs']:check(R/x['path'],x['sha256'],x['bytes'])
 q=load(I/'queue-r722.json');res=load(I/'reserved-ids-r722.json');ids=[x['mathdb_id'] for x in q]
 assert len(ids)==len(set(ids))==50 and ids==res['ids'] and res['coverage_baseline']==8933
 cov=load(I/'coverage-delta.json');assert len(cov)==8933
 active=load(I/'active-breadth-reservations.json');assert len(active)==3
 assert {x['lane'] for x in active}=={'sol-mathdb-primary-qualified-breadth-r720','sol-mathdb-primary-qualified-breadth-r722','claude-mathdb-primary-qualified-breadth-r628'}
 for j,x in enumerate(active):
  s=set(x['ids']);assert len(s)==50 and not s&set(map(int,cov)) and not s&set(res['protected_ids'])
  for y in active[:j]:assert not s&set(y['ids'])
 literals=load(D/'literal-records.json');dis=load(D/'dispositions.json')
 assert [x['mathdb_id'] for x in literals]==ids==[x['mathdb_id'] for x in dis]
 for x,d in zip(literals,dis):
  p=pathlib.Path(x['corpus_path']);assert str(p) in {str(R/z['path']) for z in chunks}
  with p.open('rb') as f:
   for n,line in enumerate(f,1):
    if n==x['line']:break
   else:raise AssertionError('line missing')
  z=json.loads(line);assert z==x['record'] and z['mathdb_id']==x['mathdb_id']
  h=digest(json.dumps(z,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  assert h==x['canonical_record_sha256']==d['canonical_record_sha256']
  assert digest(line)==x['literal_line_sha256']==d['literal_line_sha256']
  assert z['statement']==d['statement'] and digest(d['statement'].encode())==d['statement_utf8_sha256']
  assert d['classification'] in ['complete','definition-dependent','scope-ambiguous','incomplete']
  assert all(d[k] for k in ['classification_reason','quantifier_scope','technical_assessment','disposition'])
  assert d['accepted_credit']==0 and not d['prior_cleared']
 assert len(load(D/'proposals.json'))<=3
 for x in load(D/'source-provenance.json'):
  if 'error' not in x:check(D/x['path'],x['sha256'],x['size'])
 for x in load(D/'derivative-bindings.json'):check(D/x['path'],x['sha256'],x['size'])
 print(json.dumps(dict(integrity='PASS',assigned_literal_reviews=50,baseline=8933,corpus_chunks=20,frozen_inputs=8,direct_pairs=len(pairs),reserved_sets=3,proposals=len(load(D/'proposals.json')),scientific_acceptance=False,novelty='HOLD')))
if __name__=='__main__':
 try:main()
 except Exception as e:print('FAIL '+repr(e),file=sys.stderr);sys.exit(1)
