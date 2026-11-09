import itertools as it,json,sys
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def compute(m,n):
 N=m+n;full=(1<<N)-1;part=(1<<m)-1;basis=[{}for _ in range(N+1)];comps={}
 for s in range(1,1<<N):
  c=[s] if s&part and s&(full^part) else [1<<i for i in range(N)if s>>i&1];comps[s]=c
  for v in c:basis[s.bit_count()][s,v]=len(basis[s.bit_count()])
 ranks=[0]*(N+1)
 for k in range(1,N):
  piv={}
  for (s,c),col in basis[k].items():
   v=0
   for a in range(N):
    if s>>a&1:continue
    ss=s|1<<a;cc=next(x for x in comps[ss]if x&c)
    v^=1<<basis[k+1][ss,cc]
   while v:
    b=v.bit_length()-1
    if b in piv:v^=piv[b]
    else:piv[b]=v;break
  ranks[k]=len(piv)
 dims=[len(b)for b in basis];hom=[dims[k]-ranks[k]-(ranks[k-1]if k else 0)for k in range(N+1)]
 return dict(m=m,n=n,chain_dims=dims,differential_ranks=ranks,homology_dims=hom,expected=hom[2]==1 and sum(hom)==1)
out=[]
for N in range(4,int(sys.argv[1])+1):
 for m in range(2,N//2+1):
  r=compute(m,N-m);print(r,flush=True);out.append(r);(D/'outputs/uber.json').write_text(json.dumps(out,indent=2)+'\n')
