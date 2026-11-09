# ILS restricted to vertices v with D(v)=4xz-y^2 in {0,c}; report best per c.
import sys,os,itertools,time
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from ils import ils
p=int(sys.argv[1]); secs=float(sys.argv[2]); cs=[int(x) for x in sys.argv[3].split(',')]
S=set()
for a in range(p):
    for b in range(p):
        if a or b:
            s=((a*a)%p,(2*a*b)%p,(b*b)%p); S.add(s); S.add(tuple((-c)%p for c in s))
sq={(x*x)%p for x in range(1,p)}
for c in cs:
    V=[v for v in itertools.product(range(p),repeat=3) if (4*v[0]*v[2]-v[1]*v[1])%p in (0,c)]
    idx={v:i for i,v in enumerate(V)}; N=len(V); adj=[0]*N
    for i,v in enumerate(V):
        for s in S:
            w=tuple((a+b)%p for a,b in zip(v,s))
            j=idx.get(w)
            if j is not None: adj[i]|=1<<j
    best,it=ils(adj,N,secs,c)
    print('p',p,'c',c,'square' if c in sq else 'nonsquare','|D^-1{0,c}|',N,'best',len(best),'q^2',p*p,flush=True)
