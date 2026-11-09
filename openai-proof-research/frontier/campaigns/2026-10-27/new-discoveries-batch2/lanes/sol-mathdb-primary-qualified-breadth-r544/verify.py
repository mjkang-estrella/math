#!/usr/bin/env python3
"""Independent read-only integrity verifier. Invoke under the fixed helper_guard.py."""
import pathlib,json,hashlib,sys
D=pathlib.Path(__file__).resolve().parent
EX={'manifest.json','final-verification-receipt.json'}
def load(p):return json.loads(p.read_text())
def digest(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'size mismatch: {p}'
 assert digest(b)==e['sha256'],f'hash mismatch: {p}'
def payload(root):
 m=load(root/'manifest.json');assert set(m['excluded_exact_paths'])==EX
 es=m['files'];names=[e['path'] for e in es];assert len(names)==len(set(names))
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
 assert actual-set(EX)==set(names),'extra/missing payload file'
 for e in es:
  assert not pathlib.Path(e['path']).is_absolute() and '..' not in pathlib.Path(e['path']).parts
  check(root/e['path'],e)
 return len(es)
def main():
 if len(sys.argv)==3 and sys.argv[1]=='--payload-only':
  print(json.dumps({'payload_files':payload(pathlib.Path(sys.argv[2]))}));return
 assert len(sys.argv)==1
 count=payload(D);L=D.parent;I=L/'root-mathdb-breadth-intake-r543';R=L/'pi-mathdb-full-corpus-inventory-r301'
 bs=load(D/'flat-bindings.json');by={e['path']:e for e in bs};assert len(by)==len(bs)
 for e in bs:check(pathlib.Path(e['path']),e)
 im=load(I/'manifest.json');actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}
 assert actual=={e['path'] for e in im['files']}|set(im['excluded_exact_paths'])
 for e in im['files']:check(I/e['path'],e)
 for e in load(I/'bindings.json'):
  check(pathlib.Path(e['original']),e);check(pathlib.Path(e['copy']),e)
 # Inventory manifest must have been bound by intake, not merely by this lane.
 inv=[e for e in load(I/'bindings.json') if e['original']==str(R/'manifest.json')];assert len(inv)==1;check(R/'manifest.json',inv[0])
 rm=load(R/'manifest.json');chunks=[e for e in rm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(rm['frozen_inputs'])==8
 for e in chunks+rm['frozen_inputs']:check(R/e['path'],e)
 for name in ['accepted-exclusions.json','historical-dispositions.json']:
  e=next(e for e in rm['frozen_inputs'] if e['path']=='frozen/'+name);check(L/'root-mathdb-accepted-exclusions-r304'/name,e)
 q=load(I/'queue.json');res=load(I/'reserved-ids.json');cov=load(I/'coverage-delta.json');act=load(I/'active-breadth-reservations.json')
 ids={e['mathdb_id'] for e in q};assert len(q)==len(ids)==50 and ids==set(res['ids']) and res['lane']==D.name and len(cov)==res['coverage_baseline']==4533
 sets=[set(e['ids']) for e in act];assert len(sets)==3 and sum(s==ids for s in sets)==1
 assert set(res['other_active_reservations'])==set.union(*(s for s in sets if s!=ids))
 for i,s in enumerate(sets):
  assert len(s)==50 and not s&set(map(int,cov)) and not s&set(res['protected_ids'])
  for t in sets[:i]:assert not s&t
 assert res['active_hypothesis_ids']==[]
 found={}
 for e in chunks:
  p=R/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:
    assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(str(p),n,r)
 rows=load(D/'assigned-records.json');ds=load(D/'dispositions.json');assert len(rows)==len(ds)==50 and {d['mathdb_id'] for d in ds}==ids
 assert len({d['mathdb_id'] for d in ds})==50 and set(found)==ids
 for r in rows:
  p,n,orig=found[r['mathdb_id']];assert r['chunk']==p and r['line']==n and r['record']==orig
  assert r['statement']==orig['statement'] and r['statement_sha256']==digest(orig['statement'].encode())
  assert r['canonical_record_sha256']==digest(json.dumps(orig,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  d=next(d for d in ds if d['mathdb_id']==r['mathdb_id'])
  for k in ['chunk','line','statement','statement_sha256','canonical_record_sha256']:assert d[k]==r[k]
  assert d['literal_statement_read'] and d['technical_reading'] and d['accepted_credit']==0 and not d['prior_cleared']
 assert load(D/'proposals.json')==[]
 for e in load(D/'source-excerpts.json'):
  lines=pathlib.Path(e['path']).read_text().splitlines(keepends=True);t=''.join(lines[e['start_line']-1:e['end_line']]);assert t==e['text'] and digest(t.encode())==e['utf8_sha256']
 for e in load(D/'source-bindings.json'):
  if 'path' in e:check(pathlib.Path(e['path']),e)
 print(json.dumps({'integrity':'PASS','payload_files':count,'flat_original_bindings':len(bs),'intake_exact_payload':'PASS','original_copy_pairs':'PASS','original_corpus_chunks':20,'frozen_inputs':8,'reservations':'3x50 disjoint from 4533 and protected IDs','literal_records':50,'proposals':0,'math_novelty':'NOT VERIFIED; HOLD','manifest_sha256':digest((D/'manifest.json').read_bytes()),'manifest_size':(D/'manifest.json').stat().st_size}))
if __name__=='__main__':
 try:main()
 except Exception as e:
  print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
