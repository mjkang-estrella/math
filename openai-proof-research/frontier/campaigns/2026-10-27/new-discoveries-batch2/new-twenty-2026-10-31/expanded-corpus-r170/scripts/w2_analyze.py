import sys,itertools
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from dp_sweep_lib import parse
from w2 import mis_list,pc
g=sys.argv[1]; adj=parse(g); n=len(adj); nb=[sum(1<<w for w in a) for a in adj]
E=[(i,j) for i in range(n) for j in adj[i] if i<j]
print('n',n,'m',len(E),'degrees',[len(a) for a in adj])
print('edges',E)
print('complement edges',[(i,j) for i in range(n) for j in range(i+1,n) if j not in adj[i]])
Ms=mis_list(n,nb,(1<<n)-1)
bits=lambda x:[v for v in range(n) if x>>v&1]
print('maximal independent sets',sorted([bits(M) for M in Ms],key=len))
for v in range(n):
    G2=[w for w in range(n) if w!=v]
    Ms2=mis_list(n,nb,((1<<n)-1)&~(1<<v)); print('G-%d sizes'%v,sorted({pc(M) for M in Ms2}))
