import itertools,json,pathlib
L=pathlib.Path(__file__).resolve().parent
spaces={frozenset([0])}
for d in range(4):
 for s in list(spaces):
  for v in range(16):spaces.add(s|frozenset(x^v for x in s))
assert len(spaces)==67
def mat(v):return [[v>>0&1,v>>1&1],[v>>2&1,v>>3&1]]
def enc(a):return sum(a[i][j]<<(2*i+j) for i in range(2) for j in range(2))
def mul(a,b):return [[sum(a[i][k]*b[k][j] for k in range(2))%2 for j in range(2)] for i in range(2)]
gl=[mat(v) for v in range(16) if ((v&1)*((v>>3)&1)^((v>>1)&1)*((v>>2)&1))==1];assert len(gl)==6
maps=[[enc(mul(mul(a,mat(v)),b)) for v in range(16)] for a in gl for b in gl]
unseen=spaces-{frozenset([0])};orbits=[]
while unseen:
 s=min(unseen,key=lambda x:(len(x),sorted(x)));orb={frozenset(g[v] for v in s) for g in maps};assert orb<=unseen
 orbits.append(dict(representative=sorted(s),size=len(orb),dimension=len(s).bit_length()-1));unseen-=orb
assert len(orbits)==10
out=dict(status='PASS',scope='67 row subspaces of F2^4 under 36 left-right GL2 actions; ten nonzero orbits only. Not Table 5 ranks/minimal-representative certification; not novelty proof.',orbits=orbits)
(L/'bounded-checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
