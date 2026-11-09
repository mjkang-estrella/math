#!/usr/bin/env python3
"""Read-only independent verifier. Run under the required fixed helper guard."""
import pathlib,json,hashlib,sys
P=pathlib.Path(sys.argv[1]).resolve() if len(sys.argv)>1 else pathlib.Path(__file__).resolve().parent
L=pathlib.Path(__file__).resolve().parent.parent;I=L/'root-mathdb-breadth-intake-r547';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'size mismatch: {p}';assert h(b)==e['sha256'],f'hash mismatch: {p}'
def exact(root,m,excluded):
 assert len({e['path'] for e in m['files']})==len(m['files'])
 assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(excluded)=={e['path'] for e in m['files']},f'exact payload mismatch: {root}'
 for e in m['files']:check(root/e['path'],e)
def verify():
 m=j(P/'manifest.json');assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json'];exact(P,m,m['excluded_exact_paths'])
 for e in j(P/'flat-bindings.json')+j(P/'source-bindings.json'):check(pathlib.Path(e['path']),e)
 exact(I,j(I/'manifest.json'),['manifest.json','verification-receipt.json'])
 for e in j(I/'bindings.json'):
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 check(C/'manifest.json',next(e for e in j(I/'bindings.json') if e['original']==str(C/'manifest.json')))
 cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==4633
 active=j(I/'active-breadth-reservations.json');seen=set();protected=set(j(I/'reserved-ids.json')['protected_ids'])
 for r in active:
  s=set(r['ids']);assert len(s)==50 and not s&seen and not s&set(map(int,cov)) and not s&protected;seen|=s
 assert len(seen)==150
 for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
 ids=set(j(I/'reserved-ids.json')['ids']);assert {r['mathdb_id'] for r in j(I/'queue.json')}==ids
 ds=j(P/'dispositions.json');assert len(ds)==50 and {d['mathdb_id'] for d in ds}==ids
 found={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(str(p),n,r)
 assert len(found)==50
 for d in ds:
  p,n,r=found[d['mathdb_id']];assert d['chunk']==p and d['line']==n and d['statement']==r['statement'];assert d['statement_sha256']==h(r['statement'].encode());assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode());assert d['accepted_credit']==0 and d['literal_statement_read'] and not d['current_registry_cleared'] and not d['full_dependency_audit']
 for r in j(P/'assigned-records.json'):
  _,_,original=found[r['mathdb_id']];assert r['record']==original
 assert j(P/'proposals.json')==[]
 for e in j(P/'downloads.json'):
  if 'failure' not in e:
   check(P/e['name'],e)
   if 'derivative' in e:check(P/pathlib.Path(e['derivative']['path']).name,e['derivative'])
 print(json.dumps({'integrity':'PASS','literal_rows':50,'original_chunks':20,'frozen_inputs':8,'baseline':4633,'reserved_total':150,'proposals':0,'math_novelty':'HOLD; not certified by integrity'}))
if __name__=='__main__':
 try:verify()
 except Exception as ex:print(str(ex),file=sys.stderr);sys.exit(1)
