import pathlib,json,itertools,collections
L=pathlib.Path(__file__).resolve().parent
r=json.loads((L/'cube-certificate.json').read_text());Z=set(r['z']);X=set(r['x']);Y=set(r['y']);a=r['a'];b=r['b'];n=5
assert X==Z-{a} and Y==Z-{b} and len(X)==len(Y)==5
def dist(v,w):return (v^w).bit_count()
def prof(v):return [sum(dist(v,w)==d for w in Z) for d in range(6)]
g=lambda v:r['t']^sum(((v>>i)&1)<<r['p'][i] for i in range(n))
assert {g(v) for v in X}==Y
assert [v for v in Z if prof(v)==prof(13)]==[13]
assert dist(a,13)==1 and dist(b,13)==4
stabilizers=[];transports=[];count=0
for p in itertools.permutations(range(n)):
 for t in range(1<<n):
  h=lambda v:t^sum(((v>>i)&1)<<p[i] for i in range(n))
  count+=1
  if {h(v) for v in Z}==Z:
   stabilizers.append([p,t]);assert {h(v) for v in X}!=Y
  if {h(v) for v in X}==Y:transports.append([p,t])
assert count==3840 and transports
out=dict(status='PASS',group_elements=count,stabilizers=stabilizers,transports=transports,mapping={str(v):g(v) for v in sorted(X)},distance_matrix=[[dist(v,w) for w in sorted(Z)] for v in sorted(Z)],profiles={str(v):prof(v) for v in sorted(Z)},scope='exact dimension-5 certificate; all-n>=5 extension is proved in PROOF.md, not inferred by finite test')
(L/'math-verification.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
