"""Independent read-only integrity verifier. Run through the fixed helper guard."""
from pathlib import Path
import json,hashlib,sys
P=Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r517';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'size: {p}';assert h(b)==e['sha256'],f'hash: {p}'
def exact(root,m,negative=None):
 excluded=set(m['excluded_exact_paths']);assert excluded=={'manifest.json',('final-verification-receipt.json' if root==P else 'verification-receipt.json')}
 names={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-excluded
 if negative=='extra':names.add('__in_memory_unlisted_file__')
 assert len(m['files'])==len({e['path'] for e in m['files']})
 assert names=={e['path'] for e in m['files']},'exact payload mismatch'
 for n,e0 in enumerate(m['files']):
  e=dict(e0)
  if n==0 and negative=='hash':e['sha256']='0'*64
  if n==0 and negative=='size':e['size']+=1
  check(root/e['path'],e)
def main():
 # Negative cases modify only expected values in memory, never originals.
 case=sys.argv[2] if len(sys.argv)==3 and sys.argv[1]=='--negative' else None
 exact(P,j(P/'manifest.json'),case)
 for e in j(P/'flat-bindings.json'):check(Path(e['path']),e)
 exact(I,j(I/'manifest.json'))
 for e in j(I/'bindings.json'):
  for k in ('original','copy'):check(Path(e[k]),e)
 cm=j(C/'manifest.json')
 ce=next(e for e in j(I/'manifest.json')['files'] if e['path']=='frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json');check(C/'manifest.json',ce)
 chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')]
 assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==3983
 active=j(I/'active-breadth-reservations.json');seen=set()
 for r in active:
  ids=set(r['ids']);assert len(ids)==len(r['ids'])==50
  assert not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
 assert len(seen)==150
 res=j(I/'reserved-ids.json');ids=set(res['ids']);q=j(I/'queue.json')
 assert ids=={r['mathdb_id'] for r in q} and len(ids)==50
 assert res['lane']==P.name
 assert next(r for r in active if r['lane']==P.name)['ids']==res['ids']
 assert not ids&set(res['other_active_reservations']) and not ids&set(res['protected_ids'])
 route=[json.loads(s) for s in (I/'routing-queue.jsonl').open()];assert len(route)==6000
 assert (I/'routing-queue.jsonl').read_bytes()==(I/'frozen/root-mathdb-breadth-intake-r515/routing-queue.jsonl').read_bytes()
 indexed={r['mathdb_id']:r for r in route}
 assert all(r==indexed[r['mathdb_id']] for r in q)
 found={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:
    assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(str(p),n,r)
 ds=j(P/'dispositions.json');ars=j(P/'assigned-records.json')
 assert len(ds)==len(ars)==50 and {d['mathdb_id'] for d in ds}==ids and len({d['mathdb_id'] for d in ds})==50
 for d in ds+ars:
  path,n,r=found[d['mathdb_id']]
  assert d['corpus_chunk']==path and d['corpus_line']==n and d['statement']==r['statement']
  assert d['statement_utf8_sha256']==h(r['statement'].encode())
  assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  if 'record' in d:assert d['record']==r
 for d in ds:assert d['accepted_credit']==0 and d['current_registry_cleared'] is False and d['literal_statement_read'] is True
 assert j(P/'proposals.json')==[]
 for filename in ['source-bindings.json','derivative-bindings.json']:
  for e in j(P/filename):check(Path(e['path']),e)
 assert len(j(P/'source-bindings.json'))==len(j(P/'derivative-bindings.json'))==4
 print(json.dumps(dict(integrity='PASS',literal_reviews=50,proposals=0,baseline=3983,original_corpus_chunks=20,frozen_inputs=8,direct_pairs=len(j(I/'bindings.json')),reservations=150,scientific_acceptance=False)))
if __name__=='__main__':
 try:main()
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
