import itertools,pathlib,json,sys
D=pathlib.Path(__file__).resolve().parents[1]
for mods in [(3,),(4,),(5,),(6,),(7,),(8,),(3,3),(2,4),(2,5)]:
 g=list(itertools.product(*[range(m) for m in mods]));idx={x:i for i,x in enumerate(g)};n=len(g);N=2*n
 mul=lambda a,b:(a//n ^ b//n)*n+idx[tuple((x+(-1 if a//n else 1)*y)%m for x,y,m in zip(g[a%n],g[b%n],mods))]
 inv=[next(b for b in range(N) if mul(a,b)==0) for a in range(N)]
 plus=[[1<<mul(a,b) for b in range(N)] for a in range(N)];minus=[[1<<mul(a,inv[b]) for b in range(N)] for a in range(N)];counts=[0,0,0]
 for bits in range(1<<N):
  aa=[a for a in range(N) if bits>>a&1];s=d=0
  for a in aa:
   for b in aa:s|=plus[a][b];d|=minus[a][b]
  counts[(s.bit_count()>d.bit_count())-(s.bit_count()<d.bit_count())+1]+=1
 print(json.dumps({'abelian_factors':mods,'group_order':N,'subsets':1<<N,'MDTS_balanced_MSTD':counts}),flush=True)
