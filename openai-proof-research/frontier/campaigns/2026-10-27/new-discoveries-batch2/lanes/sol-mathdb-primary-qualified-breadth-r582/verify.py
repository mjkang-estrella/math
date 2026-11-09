#!/usr/bin/env python3
"""Independent read-only integrity checker. Run through the fixed helper_guard.py."""
from pathlib import Path
import json,hashlib,sys
D=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else Path(__file__).resolve().parent
L=Path(__file__).resolve().parent.parent;I=L/'root-mathdb-breadth-intake-r581';R=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def check(p,x):
 b=p.read_bytes();assert len(b)==x.get('size',x.get('bytes')),f'size mismatch: {p}';assert hashlib.sha256(b).hexdigest()==x['sha256'],f'hash mismatch: {p}'
def payload(root,m):
 expected={x['path'] for x in m['files']};excluded=set(m['excluded_exact_paths']);assert expected.isdisjoint(excluded)
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()};assert actual-excluded==expected,f'exact payload mismatch: {actual-excluded ^ expected}'
 for x in m['files']:check(root/x['path'],x)
def main():
 m=j(D/'manifest.json');assert set(m['excluded_exact_paths'])=={'manifest.json','final-verification-receipt.json'};payload(D,m)
 for x in j(D/'flat-bindings.json'):check(Path(x['path']),x)
 check(I/'manifest.json',{'size':9385,'sha256':'8e88a0e56f05c72af9c69c4f412ecc2b8750cfaa3ad973842a8a509bad0e9497'});payload(I,j(I/'manifest.json'))
 for x in j(I/'bindings.json'):
  check(Path(x['original']),x);check(Path(x['copy']),x)
 rm=j(R/'manifest.json');chunks=[x for x in rm['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20 and len(rm['frozen_inputs'])==8
 for x in chunks+rm['frozen_inputs']:check(R/x['path'],x)
 s=j(I/'reserved-ids.json');ids=set(s['ids']);q=j(I/'queue.json');cov=j(I/'coverage-delta.json');a=j(I/'active-breadth-reservations.json');sets=[set(x['ids']) for x in a]
 assert len(ids)==len(q)==50 and ids=={x['mathdb_id'] for x in q};assert s['lane']=='sol-mathdb-primary-qualified-breadth-r582';assert len(cov)==s['coverage_baseline']==5483
 assert len(sets)==3 and all(len(t)==50 for t in sets) and ids in sets;assert len(set.union(*sets))==150
 assert all(not t&set(map(int,cov)) and not t&set(s['protected_ids']) for t in sets)
 assert set(s['other_active_reservations'])==set.union(*[t for t in sets if t!=ids])
 assert {x['lane'] for x in a}=={'claude-mathdb-primary-qualified-breadth-r504','sol-mathdb-primary-qualified-breadth-r578',s['lane']}
 rows=j(D/'literal-records.json');ds=j(D/'dispositions.json');assert len(rows)==len(ds)==50 and {x['mathdb_id'] for x in ds}==ids
 lookup={x['mathdb_id']:x for x in ds};found=set()
 for c in chunks:
  p=R/c['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line);i=r['mathdb_id']
   if i not in ids:continue
   assert i not in found;found.add(i);d=lookup[i]
   x=next(z for z in rows if z['record']['mathdb_id']==i)
   assert x['record']==r and x['line']==n and x['corpus_chunk']==str(p)
   assert d['corpus_line']==n and d['corpus_chunk']==str(p) and d['exact_statement_utf8']==r['statement']
   assert d['statement_utf8_sha256']==hashlib.sha256(r['statement'].encode()).hexdigest()
   assert d['canonical_record_sha256']==hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()
   assert d['scope_flags']['literal_record_statement_read'] and d['scope_flags']['accepted_credit']==0
 assert found==ids and len(j(D/'proposals.json'))<=3
 for name in ['source-provenance.json','derivative-bindings.json']:
  for x in j(D/name):
   if 'sha256' in x:check(D/x['file'],x)
 print(json.dumps({'integrity':'PASS','assigned_literal_records':50,'baseline_record_reviews':5483,'chunks_checked_in_place':20,'frozen_inputs_checked':8,'proposals':len(j(D/'proposals.json')),'math_or_novelty_pass':False}))
if __name__=='__main__':
 try:main()
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
