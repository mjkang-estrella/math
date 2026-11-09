import pathlib,hashlib,json,itertools,time
from fractions import Fraction as F
L=pathlib.Path(__file__).resolve().parent;start=time.monotonic()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'manifest.json').read_text());assert 'manifest.json' not in m and 'verification-receipt.json' not in m
for p,h in m.items():assert sha(L/p)==h,p
assert set(m)=={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
scientific=0
for b in json.loads((L/'freeze-bindings.json').read_text()):
 if 'missing' in b:continue
 assert sha(pathlib.Path(b['copy']))==b['sha256']
 if b['kind'].startswith('scientific'):
  assert sha(pathlib.Path(b['original']))==b['sha256'];scientific+=1
for line in (L/'sourcebindings.jsonl').read_text().splitlines():
 b=json.loads(line);assert sha(pathlib.Path(b['source']))==b['source_sha256']
 if 'copy' in b:assert sha(pathlib.Path(b['copy']))==b['source_sha256']
 if 'text' in b:assert sha(pathlib.Path(b['text']))==b['text_sha256']
for line in (L/'access.jsonl').read_text().splitlines():
 b=json.loads(line)
 if 'sha256' in b:assert sha(L/'primary'/b['key'])==b['sha256']
def kernel(ps,rel):
 n=len(ps[0]);idx={p:i for i,p in enumerate(ps)};A=[[F(0) for _ in ps] for _ in ps]
 for z,p in enumerate(ps):
  for i,j in itertools.product(range(n),repeat=2):
   q=list(p)
   for k in (range(i,j) if i<j else range(i-1,j-1,-1)):
    if (q[k],q[k+1]) not in rel and (q[k+1],q[k]) not in rel:q[k],q[k+1]=q[k+1],q[k]
   A[z][idx[tuple(q)]]+=F(1,n*n)
 return A
ps=[(0,1,2),(0,2,1),(2,0,1)];M=kernel(ps,{(0,1)});v=[1,0,-1]
H=[[F(0) for _ in ps] for _ in ps]
for x in range(3):
 for i,p in enumerate(ps):
  f=[j for j,q in enumerate(ps) if tuple(t for t in p if t!=x)==tuple(t for t in q if t!=x)]
  for j in f:H[i][j]+=F(1,3*len(f))
def action(A,v):return [sum(a*b for a,b in zip(r,v)) for r in A]
assert action(M,v)==[F(4,9)*x for x in v]
assert action(H,v)==[F(1,2)*x for x in v]
record=json.loads((L/'fiber-detail.json').read_text());assert [[str(a) for a in row] for row in M]==record['M'];assert [[str(a) for a in row] for row in H]==record['H']
ps=list(itertools.permutations(range(3)));A=kernel(ps,set());S=[[F(0) for _ in ps] for _ in ps]
for rel in [{(0,1)},{(1,0)}]:
 sub=[p for p in ps if all(p.index(a)<p.index(b) for a,b in rel)];K=kernel(sub,rel)
 for i,p in enumerate(sub):
  for j,q in enumerate(sub):S[ps.index(p)][ps.index(q)]=K[i][j]
D=[[S[i][j]-A[i][j] for j in range(6)] for i in range(6)]
assert D[0][0]==D[4][4]==F(2,9) and D[0][4]==0
assert D[1][1]*D[4][4]-D[1][4]**2<0
def rank(A):
 A=[r[:] for r in A];k=0
 for j in range(len(A[0])):
  pivot=next((i for i in range(k,len(A)) if A[i][j]),None)
  if pivot is None:continue
  A[k],A[pivot]=A[pivot],A[k];d=A[k][j];A[k]=[x/d for x in A[k]]
  for i in range(len(A)):
   if i!=k:
    t=A[i][j];A[i]=[x-t*y for x,y in zip(A[i],A[k])]
  k+=1
 return k
assert rank(D)==3 # >=2 positive and >=1 negative then inertia exactly(2,1,3).
b=json.loads((L/'exact-capped-checks.json').read_text());assert b['A_controls']==46 and b['B_splits']==2
assert [[str(a) for a in row] for row in D]==b['B_obstruction']['difference']
receipt=dict(status='PASS',manifest_sha256=sha(L/'manifest.json'),files_verified=len(m),scientific_original_copy_bindings_verified=scientific,checks=['all manifest hashes and file set','local scientific originals/copies before-after unchanged','remote body and text derivation hashes','independent literal3-state M/H reconstruction and exact Rayleigh witness','independent6-state split reconstruction; positive principal minor, negative minor, rank3 certify inertia(2,1,3)'],limits='designated guard AS/RSS512MiB CPU210 wall230, no raises',elapsed_seconds=time.monotonic()-start,not_certified=['all-n conjecture','novelty clearance','perfect process discipline; see failures.md'])
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt))
