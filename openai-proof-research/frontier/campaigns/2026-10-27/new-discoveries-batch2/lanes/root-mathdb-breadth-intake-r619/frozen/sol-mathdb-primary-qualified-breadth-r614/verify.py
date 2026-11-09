#!/usr/bin/env python3
"""Independent read-only verifier. No imports of upstream executables."""
from pathlib import Path
import json,hashlib,sys
L=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else Path(__file__).resolve().parent
I=Path(__file__).resolve().parent.parent/'root-mathdb-breadth-intake-r613';R=I.parent/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def digest(b):return hashlib.sha256(b).hexdigest()
def check(p,h,n):
 b=p.read_bytes();assert len(b)==n,('SIZE',str(p));assert digest(b)==h,('HASH',str(p))
def payload(root,m,excluded):
 paths=[x['path'] for x in m['files']];assert len(paths)==len(set(paths));assert all(not Path(p).is_absolute() and '..' not in Path(p).parts for p in paths)
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
 assert actual-set(excluded)==set(paths),('EXTRA_OR_MISSING',sorted(actual-set(excluded)-set(paths)),sorted(set(paths)-actual))
 for x in m['files']:check(root/x['path'],x['sha256'],x.get('size',x.get('bytes')))
m=load(L/'manifest.json');assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json'];payload(L,m,m['excluded_exact_paths'])
for x in load(L/'flat-bindings.json'):check(Path(x['path']),x['sha256'],x['size'])
check(I/'manifest.json','de5ee96819d21bc91207fb423373ad2150aa5165940b3930fc20123485882114',10280)
payload(I,load(I/'manifest.json'),['manifest.json','verification-receipt.json'])
for x in load(I/'bindings.json'):
 for k in ['original','copy']:check(Path(x[k]),x['sha256'],x['bytes'])
check(R/'manifest.json','4da10b6dcd6d56a34399195f26abe9ff13f8c3fd67e88b672fc35db2a2a71e15',22047)
rm=load(R/'manifest.json');chunks=[x for x in rm['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20 and len(rm['frozen_inputs'])==8
for x in chunks+rm['frozen_inputs']:check(R/x['path'],x['sha256'],x['bytes'])
q=load(I/'queue-r614.json');ids={x['mathdb_id'] for x in q};assert len(q)==len(ids)==50
res=load(I/'reserved-ids-r614.json');assert ids==set(res['ids'])
cov=set(map(int,load(I/'coverage-delta.json')));assert len(cov)==6283;seen=set();active=load(I/'active-breadth-reservations.json');assert len(active)==3
for r in active:
 s=set(r['ids']);assert len(s)==len(r['ids'])==50;assert not(s&seen or s&cov or s&set(r['protected_ids']));seen|=s
assert ids==set(next(r for r in active if r['lane']==L.name or r['lane']=='sol-mathdb-primary-qualified-breadth-r614')['ids'])
rows=load(L/'literal-records.json');ds=load(L/'dispositions.json');assert len(rows)==len(ds)==50
assert {d['mathdb_id'] for d in ds}==ids
found={}
for x in chunks:
 p=R/x['path']
 for n,b in enumerate(p.open('rb'),1):
  d=json.loads(b)
  if d['mathdb_id'] in ids:assert d['mathdb_id'] not in found;found[d['mathdb_id']]=(d,str(p),n)
assert set(found)==ids
for x in rows:
 d=x['record'];i=d['mathdb_id'];original,p,n=found[i];assert d==original and (x['chunk'],x['line'])==(p,n)
 h=digest(json.dumps(original,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode());assert h==x['canonical_record_sha256']
 r=next(r for r in ds if r['mathdb_id']==i)
 assert (r['corpus_chunk'],r['corpus_line'])==(p,n)
 assert r['canonical_record_sha256']==h and r['exact_utf8_statement']==original['statement'] and r['statement_utf8_sha256']==digest(original['statement'].encode())
 assert r['literal_record_review'] is True and r['accepted_credit']==0 and not r['current_registry_cleared']
 assert sum(bool(r[k]) for k in ['complete_statement','incomplete_record','missing_definitions','ambiguous_scope'])==1
assert load(L/'proposals.json')==[]
for x in load(L/'source-provenance.json'):
 if 'path' in x:check(L/x['path'],x['sha256'],x['size'])
for x in load(L/'derivative-bindings.json'):check(L/x['path'],x['sha256'],x['size'])
print(json.dumps({'integrity':'PASS','literal_reviews':50,'complete_statements':sum(d['complete_statement'] for d in ds),'original_chunks':20,'frozen_inputs':8,'reservation_sets':3,'baseline':6283,'proposals':0,'math_and_novelty':'HOLD; not certified by integrity'}))
