import sys, json, pathlib
from fractions import Fraction as F
reps=json.loads(pathlib.Path(sys.argv[1]).read_text())
for n in range(2,int(sys.argv[2])+1):
    cnt=0; best=None
    for E in reps[str(n)]:
        adj=[[] for _ in range(n)]
        for i,j in E: adj[i].append(j); adj[j].append(i)
        ecc=[]
        for s in range(n):
            d=[-1]*n; d[s]=0; q=[s]
            for v in q:
                for u in adj[v]:
                    if d[u]<0: d[u]=d[v]+1; q.append(u)
            if min(d)<0: break
            ecc.append(max(d))
        else:
            cnt+=1; deg=[len(a) for a in adj]
            if len(E)==n-1 and max(deg)<=2 and n%2==0: continue
            H=sum(F(2,deg[i]+deg[j]) for i,j in E); D=H-min(ecc)
            if best is None or D<best[0]: best=(D,E)
    print(n,'connected',cnt,'min H-r over non-even-path',best and best[0],best and best[1])
