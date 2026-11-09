import pathlib,json,hashlib,itertools,math,datetime
L=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((L/'final-manifest.json').read_text())
assert 'final-manifest.json' not in manifest and 'verification-receipt.json' not in manifest
for rel,h in manifest.items():assert sha(L/rel)==h,rel
for r in json.loads((L/'bindings.json').read_text()):assert sha(pathlib.Path(r['original']))==r['sha256']==sha(pathlib.Path(r['copy']))
for r in map(json.loads,(L/'derived.jsonl').read_text().splitlines()):assert sha(pathlib.Path(r['source']))==r['sha256'] and sha(pathlib.Path(r['text']))==r['text_sha256']
for r in map(json.loads,(L/'access.jsonl').read_text().splitlines()):
 if 'path' in r:assert sha(pathlib.Path(r['path']))==r['sha256']
d=json.loads((L/'exact-checks.json').read_text());q=d['prime'];z=d['root'];S=d['support']
assert q>2 and all(q%i for i in range(2,math.isqrt(q)+1));assert z%q!=1 and pow(z,13,q)==1
def nonsingular(A):
 for c in range(len(A)):
  k=next((k for k in range(c,len(A)) if A[k][c]%q),None)
  if k is None:return False
  A[c],A[k]=A[k],A[c];inv=pow(A[c][c],q-2,q);A[c]=[(v*inv)%q for v in A[c]]
  for i in range(len(A)):
   if i!=c:
    t=A[i][c];A[i]=[(u-t*v)%q for u,v in zip(A[i],A[c])]
 return True
for J in itertools.combinations(range(1,13),5):assert nonsingular([[pow(z,j*s,q) for s in S] for j in J])
w=d['naive_diameter_three_rank_one_failure'];n=w['n'];steps=w['steps'];A=[{(i+j)%n for j in steps}|{(i-j)%n for j in steps} for i in range(n)]
for s,row in zip(w['sources'],w['counts']):
 ds={s:0};todo=[s]
 for v in todo:
  for u in A[v]:
   if u not in ds:ds[u]=ds[v]+1;todo.append(u)
 assert len(ds)==n and max(ds.values())==3
 for t,count in zip(w['targets'],row):
  assert ds[t]==3 and sum(t in A[b] for a in A[s] for b in A[a])==count
assert w['counts'][0][0]*w['counts'][1][1]!=w['counts'][0][1]*w['counts'][1][0]
changed=[]
for r in json.loads((L/'history-bindings.json').read_text()):
 p=pathlib.Path(r['path'])
 if not p.exists() or sha(p)!=r['sha256']:changed.append(str(p))
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha(L/'final-manifest.json'),files_verified=len(manifest),independent_exact_certificate=True,primary_originals_and_texts='PASS',frozen_originals_and_copies='PASS',historical_in_place_changed_paths=changed,history_note='Changed live reports, if any, are not novelty clearance; four relied-on frozen reports verified separately.',credit=0)
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
