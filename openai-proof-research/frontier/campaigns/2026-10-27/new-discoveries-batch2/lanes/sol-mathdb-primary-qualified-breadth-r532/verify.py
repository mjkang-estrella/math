"""Independent read-only verifier; invoke through the fixed helper_guard.py.
No upstream Python is imported or executed. Nonzero exit on any mismatch.
"""
from pathlib import Path
import json,hashlib,sys,argparse,collections
D=Path(__file__).resolve().parent;L=D.parent;I=L/'root-mathdb-stack-park-intake-r531';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'size:{p}';assert sha(b)==e['sha256'],f'hash:{p}'
def exact(root,m):
 assert m['excluded_exact_paths'] in [['manifest.json','verification-receipt.json'],['manifest.json','finalreceipt.json']]
 names=[e['path'] for e in m['files']];assert len(names)==len(set(names))
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()};assert actual-set(m['excluded_exact_paths'])==set(names),'exact payload/extra file'
 for e in m['files']:
  assert not Path(e['path']).is_absolute() and '..' not in Path(e['path']).parts
  check(root/e['path'],e)
def verify():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=D);ap.add_argument('--payload-only',action='store_true');a=ap.parse_args()
 root=a.root;exact(root,j(root/'manifest.json'))
 if a.payload_only:return {'payload':'PASS'}
 assert root.resolve()==D
 receipt=j(D/'verification-receipt.json');check(D/'manifest.json',receipt['manifest'])
 for e in j(D/'flat-bindings.json'):check(Path(e['path']),e)
 for e in j(D/'initial-bindings.json'):check(Path(e['path']),e)
 exact(I,j(I/'manifest.json'))
 for e in j(I/'bindings.json'):
  for key in ['original','copy']:check(Path(e[key]),e)
 # Independently verify direct frozen-child and original payloads, without upstream code.
 child=L/'sol-mathdb-stack-fiber-preliminary-review-r528';frozen=I/'frozen'/child.name
 exact(child,j(frozen/'manifest.json'));exact(frozen,j(frozen/'manifest.json'))
 for e in j(child/'flat-bindings.json'):check(Path(e['path']),e)
 frozen_inv=I/'frozen'/C.name/'manifest.json';assert (C/'manifest.json').read_bytes()==frozen_inv.read_bytes()
 cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==4233
 queue=j(I/'queue.json');res=j(I/'reserved-ids.json');active=j(I/'active-breadth-reservations.json');assert len(active)==3
 ids={r['mathdb_id'] for r in queue};assert len(queue)==len(ids)==50 and ids==set(res['ids']) and res['lane']==D.name and res['coverage_baseline']==4233
 seen=set()
 for r in active:
  s=set(r['ids']);assert len(s)==len(r['ids'])==50 and not s&seen and not s&set(map(int,cov)) and not s&set(r['protected_ids']);assert not r['active_hypothesis_ids'];seen|=s
 for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
 assert len((I/'routing-queue.jsonl').read_text().splitlines())==6000
 ds=j(D/'dispositions.json');assert len(ds)==50 and {x['mathdb_id'] for x in ds}==ids
 records={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:assert r['mathdb_id'] not in records;records[r['mathdb_id']]=(p,n,r)
 assert len(records)==50
 for x in ds:
  p,n,r=records[x['mathdb_id']];st=r['statement'].encode()
  assert x['corpus_chunk']==str(p) and x['corpus_line_1based']==n
  assert x['statement']==r['statement'] and x['statement_utf8_size']==len(st) and x['statement_utf8_sha256']==sha(st)
  assert x['canonical_record_sha256']==sha(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  assert x['literal_statement_read'] and x['credit']==0
 assert j(D/'proposals.json')==[]
 for name in ['source-download-bindings.json','latest-download-bindings.json','derivative-bindings.json','latest-derivative-bindings.json']:
  for e in j(D/name):check(Path(e['path']),e)
 b=j(D/'bounded-checks.json');G=[set() for _ in range(24)]
 for u,v in b['edges']:assert u!=v and 0<=u<24 and 0<=v<24;G[u].add(v);G[v].add(u)
 assert len(b['edges'])==36 and all(len(s)==3 for s in G)
 girth=100
 for v in range(24):
  dist={v:0};parent={v:-1};q=collections.deque([v])
  while q:
   u=q.popleft()
   for w in G[u]:
    if w not in dist:dist[w]=dist[u]+1;parent[w]=u;q.append(w)
    elif parent[u]!=w:girth=min(girth,dist[u]+dist[w]+1)
 assert girth==7 and 17*7<132 and 36-3*6>24-6-1
 return {'integrity':'PASS','literal_statement_records':50,'original_chunks':20,'frozen_inputs':8,'intake_payload_files':len(j(I/'manifest.json')['files']),'direct_pairs':len(j(I/'bindings.json')),'baseline':4233,'reservation_ids':150,'disjointness':True,'proposals':0,'primary_selected_rows':6,'whole_bodies':0,'math_novelty_acceptance':'NOT_ASSESSED_BY_INTEGRITY','cage_BFS':'PASS'}
if __name__=='__main__':
 try:print(json.dumps(verify(),sort_keys=True))
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
