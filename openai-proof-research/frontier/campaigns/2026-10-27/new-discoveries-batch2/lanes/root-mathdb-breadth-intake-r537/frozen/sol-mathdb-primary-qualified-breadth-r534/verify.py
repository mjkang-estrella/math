#!/usr/bin/env python3
"""Read-only verifier. Run through the fixed helper guard. No upstream verifier executed."""
from pathlib import Path
import json,hashlib,sys
D=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else Path(__file__).resolve().parent
EX={'manifest.json','final-verification-receipt.json'}
def load(p):return json.loads(p.read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def check(p,x):
 assert p.is_file() and not p.is_symlink(),str(p)
 b=p.read_bytes();assert len(b)==x.get('size',x.get('bytes')),('size',str(p));assert sha(b)==x['sha256'],('hash',str(p))
def payload(root,m,excluded):
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()};expected={x['path'] for x in m['files']}
 assert len(expected)==len(m['files']), 'duplicate manifest paths'
 assert actual-excluded==expected,('exact payload',sorted(actual-excluded-expected),sorted(expected-actual))
 for x in m['files']:check(root/x['path'],x)
def main():
 m=load(D/'manifest.json');assert set(m['excluded_exact_paths'])==EX;payload(D,m,EX)
 flat=load(D/'flat-bindings.json');bound={x['path']:x for x in flat};assert len(bound)==len(flat)
 for x in flat:check(Path(x['path']),x)
 I=next(Path(x['path']).parent for x in flat if x['path'].endswith('/root-mathdb-breadth-intake-r533/manifest.json'))
 im=load(I/'manifest.json');assert set(im['excluded_exact_paths'])=={'manifest.json','verification-receipt.json'};payload(I,im,set(im['excluded_exact_paths']))
 for x in load(I/'bindings.json'):
  for k in ('original','copy'):
   assert x[k] in bound;check(Path(x[k]),x)
 R=I.parent/'pi-mathdb-full-corpus-inventory-r301';assert str(R/'manifest.json') in bound
 rm=load(R/'manifest.json');chunks=[x for x in rm['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20 and len(rm['frozen_inputs'])==8
 for x in chunks+rm['frozen_inputs']:
  p=R/x['path'];assert str(p) in bound;check(p,x)
 r=load(I/'reserved-ids.json');q=load(I/'queue.json');ids=r['ids'];assert len(ids)==len(set(ids))==50 and [x['mathdb_id'] for x in q]==ids
 cov=load(I/'coverage-delta.json');assert len(cov)==4283 and r['coverage_baseline']==4283
 reservations=load(I/'active-breadth-reservations.json');sets=[set(x['ids']) for x in reservations];assert len(sets)==3 and all(len(s)==50 for s in sets) and set(ids) in sets
 for j,s in enumerate(sets):
  assert not s&set(map(int,cov));assert not s&set(r['protected_ids'])
  for t in sets[:j]:assert not s&t
 assert set(r['other_active_reservations'])==set.union(*(s for s in sets if s!=set(ids)))
 assert r['active_hypothesis_ids']==[]
 assert {337963,338290,339564,364119,365437,365439,366370,372627}.issubset(set(r['protected_ids']))
 a=load(D/'assigned-records.json');d=load(D/'dispositions.json');assert [x['record']['mathdb_id'] for x in a]==ids==[x['mathdb_id'] for x in d]
 original={}
 for x in chunks:
  p=R/x['path']
  for n,line in enumerate(p.open(),1):
   row=json.loads(line)
   if row['mathdb_id'] in ids:assert row['mathdb_id'] not in original;original[row['mathdb_id']]=(str(p),n,row)
 assert len(original)==50
 for x,y in zip(a,d):
  p,n,row=original[y['mathdb_id']];assert x['record']==row and x['corpus_chunk']==y['corpus_chunk']==p and x['line']==y['line']==n
  assert x['statement_sha256']==y['statement_sha256']==sha(row['statement'].encode('utf-8')) and y['statement']==row['statement']
  assert x['canonical_record_sha256']==y['canonical_record_sha256']==sha(json.dumps(row,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8'))
  assert y['accepted_credit']==0 and not y['novelty_cleared']
 assert len(load(D/'proposals.json'))<=3
 for name in ['retrieval-bindings.json','derivative-bindings.json']:
  for x in load(D/name):
   if 'error' not in x:check(D/x['path'],x)
 for name in ['prior-retrieval-bindings.json','prior-derivative-binding.json']:
  x=load(D/name)
  if 'error' not in x:check(D/x['path'],x)
 print(json.dumps(dict(integrity='PASS',scientific_acceptance=False,literal_reviews=50,baseline_reported=4283,corpus_chunks_in_place=20,frozen_inputs=8,reservation_sets=3,proposals=len(load(D/'proposals.json')),flat_references=len(flat))))
if __name__=='__main__':
 try:main()
 except Exception as e:print('FAIL '+repr(e),file=sys.stderr);sys.exit(1)
