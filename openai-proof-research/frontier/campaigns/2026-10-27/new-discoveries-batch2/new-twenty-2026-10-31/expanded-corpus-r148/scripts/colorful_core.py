import itertools,random,json,pathlib,sys
L=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(148)
def betti(sides,m):
 c=len(sides);full=(1<<m)-1;cells=[[] for _ in range(c+1)]
 for face in itertools.product([-1,0,1],repeat=c):
  cover=0
  for j,s in enumerate(face):
   if s>=0:cover|=sides[j][s]
  if cover==full:cells[face.count(-1)].append(face)
 rank=[0]*(c+2)
 rank[0]=int(bool(cells[0]))
 for d in range(1,c+1):
  idx={f:i for i,f in enumerate(cells[d-1])};basis={}
  for f in cells[d]:
   bits=0
   for i in range(c):
    if f[i]==-1:
     for b in [0,1]:bits^=1<<idx[f[:i]+(b,)+f[i+1:]]
   while bits:
    p=bits.bit_length()-1
    if p in basis:bits^=basis[p]
    else:basis[p]=bits;break
  rank[d]=len(basis)
 return ([int(not cells[0])]+[len(cells[d])-rank[d]-rank[d+1] for d in range(c+1)]),list(map(len,cells))
