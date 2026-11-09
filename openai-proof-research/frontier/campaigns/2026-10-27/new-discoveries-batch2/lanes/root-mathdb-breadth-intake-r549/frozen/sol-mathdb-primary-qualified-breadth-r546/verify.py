#!/usr/bin/env python3
"""Independent read-only integrity replay. Run under fixed helper_guard.py."""
from pathlib import Path
import json,hashlib,sys
P=Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r545';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=Path(p).read_bytes()
 if len(b)!=e.get('size',e.get('bytes')):raise ValueError('size mismatch '+str(p))
 if h(b)!=e['sha256']:raise ValueError('hash mismatch '+str(p))
def exact(root,m,extra=False):
 names=[e['path'] for e in m['files']];assert len(names)==len(set(names))
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
 if extra:actual.add('UNLISTED_NEGATIVE_FILE')
 assert actual-set(m['excluded_exact_paths'])==set(names),'exact payload mismatch'
 for e in m['files']:check(root/e['path'],e)
def main():
 mode=sys.argv[1] if len(sys.argv)>1 else ''
 m=j(P/'manifest.json');assert set(m['excluded_exact_paths'])=={'manifest.json','final-verification-receipt.json'}
 if mode=='--negative-hash':
  e=dict(m['files'][0]);e['sha256']='0'*64;check(P/e['path'],e)
 if mode=='--negative-size':
  e=dict(m['files'][0]);e['size']+=1;check(P/e['path'],e)
 exact(P,m,mode=='--negative-extra')
 for e in j(P/'flat-bindings.json'):check(e['path'],e)
 exact(I,j(I/'manifest.json'))
 for e in j(I/'bindings.json'):
  check(e['original'],e);check(e['copy'],e)
 cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==4583
 res=j(I/'reserved-ids.json');ids=set(res['ids']);assert len(ids)==50 and res['lane']==P.name
 q=j(I/'queue.json');assert len(q)==50 and {r['mathdb_id'] for r in q}==ids
 seen=set();active=j(I/'active-breadth-reservations.json');assert len(active)==3
 for r in active:
  s=set(r['ids']);assert len(s)==50 and not s&seen and not s&set(map(int,cov)) and not s&set(r['protected_ids']);seen|=s
 assert len(seen)==150
 for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
 ds=j(P/'dispositions.json');assert len(ds)==50 and {d['mathdb_id'] for d in ds}==ids
 found={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(p,n,r)
 assert len(found)==50
 assigned={a['mathdb_id']:a for a in j(P/'assigned-records.json')};assert set(assigned)==ids
 for d in ds:
  p,n,r=found[d['mathdb_id']];assert str(p)==d['corpus_chunk'] and n==d['corpus_line'];assert r['statement']==d['statement_utf8'];assert h(r['statement'].encode())==d['statement_sha256'];assert h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())==d['canonical_record_sha256'];assert assigned[d['mathdb_id']]['record']==r
  assert d['credit']==0 and d['literal_statement_read'] and not d['current_registry_cleared'] and not d['full_dependency_audit']
 assert j(P/'proposals.json')==[]
 for name in ['retrieval-bindings.json','matrix-retrieval-bindings.json','derivative-bindings.json','matrix-derivative-bindings.json']:
  for e in j(P/name):
   if 'path' in e:check(P/e['path'],e)
 print(json.dumps({'integrity':'PASS','literal_reviews':50,'baseline':4583,'corpus_chunks':20,'frozen_inputs':8,'disjoint_reservations':150,'proposals':0,'mathematical_acceptance':False,'novelty_acceptance':False,'manifest_sha256':h((P/'manifest.json').read_bytes()),'manifest_size':(P/'manifest.json').stat().st_size}))
if __name__=='__main__':
 try:main()
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
