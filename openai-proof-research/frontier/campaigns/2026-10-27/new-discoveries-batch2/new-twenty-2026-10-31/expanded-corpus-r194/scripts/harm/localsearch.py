# Capped local search for connected graphs minimizing H(G)-r(G) (excluding even paths); exact Fractions on candidates.
import sys, random, time
from fractions import Fraction as F
seed=int(sys.argv[1]); budget=float(sys.argv[2]); nmax=int(sys.argv[3]); rnd=random.Random(seed)
def stats(n,E):
    adj=[set() for _ in range(n)]
    for i,j in E: adj[i].add(j); adj[j].add(i)
    deg=[len(a) for a in adj]
    if min(deg)==0: return None
    ecc=[]
    for s in range(n):
        d=[-1]*n; d[s]=0; q=[s]
        for v in q:
            for u in adj[v]:
                if d[u]<0: d[u]=d[v]+1; q.append(u)
        if min(d)<0: return None
        ecc.append(max(d))
    if len(E)==n-1 and max(deg)<=2 and n%2==0: return None
    return sum(2.0/(deg[i]+deg[j]) for i,j in E)-min(ecc)
best=(9,None); t0=time.time(); restarts=0
while time.time()-t0<budget:
    restarts+=1
    n=rnd.randint(6,nmax); E=set((i,i+1) for i in range(n-1))
    for _ in range(rnd.randint(0,4)):
        i,j=sorted(rnd.sample(range(n),2)); E.add((i,j))
    cur=stats(n,E); cur=cur if cur is not None else 9
    T=0.3
    for it in range(1500):
        n2,E2=n,set(E); mv=rnd.random()
        if mv<0.4:
            i,j=sorted(rnd.sample(range(n2),2)); E2^={(i,j)}
        elif mv<0.6 and n2<nmax:
            v=rnd.randrange(n2); E2.add((v,n2)); n2+=1
        elif mv<0.8 and n2>4:
            v=rnd.randrange(n2); E2={(a-(a>v),b-(b>v)) for a,b in E2 if v not in (a,b)}; n2-=1
        else:
            i,j=sorted(rnd.sample(range(n2),2)); E2.add((i,j))
            a,b=sorted(rnd.sample(range(n2),2)); E2.discard((a,b))
        s=stats(n2,E2)
        if s is None: continue
        if s<cur or rnd.random()<pow(2.718,-(s-cur)/T):
            n,E,cur=n2,E2,s
            if cur<best[0]: best=(cur,(n,sorted(E)))
        T=max(0.01,T*0.997)
print('seed',seed,'restarts',restarts,'best H-r',best[0],best[1])
