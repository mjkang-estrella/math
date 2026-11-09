from pathlib import Path
import json,hashlib,datetime,sys
L=Path(__file__).resolve().parent;P=L.parent

def load(p):return json.loads(p.read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def check(p,h,n=None):
 assert p.is_file(),str(p)
 b=p.read_bytes();assert sha(b)==h,(str(p),'hash')
 if n is not None:assert len(b)==n,(str(p),'size')
 return b

def verify():
 bindings=load(L/'bindings.json')['files'];assert len({r['path'] for r in bindings})==len(bindings)
 for r in bindings:check(Path(r['path']),r['sha256'],r['size'])
 for n in ['root-mathdb-breadth-intake-r371','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
  root=P/n;m=load(root/'manifest.json');m=m['files'] if isinstance(m,dict) else m
  for r in m:check(root/r['path'],r['sha256'],r.get('size',r.get('bytes')))
 # r371's own original bindings, no history copying or recursive traversal
 for r in load(P/'root-mathdb-breadth-intake-r371/bindings.json'):check(Path(r['original']),r['sha256'],r.get('size'))
 root=P/'root-mathdb-breadth-intake-r371';ids=load(root/'reserved-ids.json')['ids'];q=load(root/'queue.json')
 assert len(ids)==len(set(ids))==len(q)==50
 ids=set(ids);assert ids=={r['mathdb_id'] for r in q}
 active={n:set(load(P/n/'reserved-ids.json')['ids']) for n in ['root-mathdb-gram-intake-r359','root-mathdb-breadth-intake-r369']}
 for s in active.values():assert not ids&s
 assert not active['root-mathdb-gram-intake-r359']&active['root-mathdb-breadth-intake-r369']
 coverage=load(root/'coverage-delta.json');assert not ids&set(map(int,coverage))
 C=P/'pi-mathdb-full-corpus-inventory-r301';chunks=[r for r in load(C/'manifest.json')['files'] if r['path'].startswith('corpus/')];assert len(chunks)==20
 corpus={}
 for ch in chunks:
  b=check(C/ch['path'],ch['sha256'],ch.get('bytes',ch.get('size')))
  for line in b.splitlines():
   r=json.loads(line);i=r.get('mathdb_id',r.get('id'))
   if i in ids:assert i not in corpus;corpus[i]=r
 rs=load(L/'records.json');ds=load(L/'dispositions.json');assert len(rs)==len(ds)==50
 assert {r['mathdb_id'] for r in rs}==ids=={r['mathdb_id'] for r in ds}==set(corpus)
 for r in rs:assert r==corpus[r['mathdb_id']]
 for r in ds:
  assert r['literal_statement']==corpus[r['mathdb_id']]['statement']
  assert r['text_sha256']==sha(r['literal_statement'].encode())
  assert r['individual_reason'] and r['evidence_level'] and r['credit']==0 and not r['complete_dependencies']
 assert load(L/'proposals.json')==[]
 for r in load(L/'sources.json'):
  if 'path' in r:check(Path(r['path']),r['sha256'],r['size']);assert not r.get('challenge')
 m=load(L/'manifest.json')['files'];expected={r['path'] for r in m}
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
 assert len(m)==len(expected) and actual==expected,('exact manifest',actual^expected)
 for r in m:check(L/r['path'],r['sha256'],r['size'])
 return dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),original_bindings=len(bindings),root_original_bindings=True,corpus_chunks=20,exact_ids=50,dispositions=50,active_disjoint=True,previous_coverage_disjoint=True,prior_coverage_entries=len(coverage),retained_sources_hashed=True,exact_payload_files=len(m),proposals=0,counts=dict(additional=9,total=39,next=40),manifest_sha256=sha((L/'manifest.json').read_bytes()))
if __name__=='__main__':
 try:
  result=verify()
  if '--receipt' in sys.argv:(L/'verification-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
  print(json.dumps(result))
 except Exception as e:
  print('FAIL '+repr(e),file=sys.stderr);raise
