# Count-based HJ(k,2) colouring instance solved by the lane's pure-Python CDCL (scripts/cdcl.py).
import sys,json,time
sys.path.insert(0,__file__.rsplit('/',1)[0])
from hj_counts import build
from cdcl import Solver
k=int(sys.argv[1]); lim=float(sys.argv[2]); sym=len(sys.argv)>3 and sys.argv[3]=='sym'
n=k-1; V,idx,cliques,stars=build(k,n); N=len(V)
rep=list(range(N))
if sym:
    for i,v in enumerate(V): rep[i]=min(i,idx[tuple(reversed(v))])
cl=[]
for st in stars: cl.append([rep[x]+1 for x in dict.fromkeys(st)])
for g in cliques:
    for a in range(len(g)):
        for b in range(a+1,len(g)):
            x,y=rep[g[a]],rep[g[b]]
            cl.append([-(x+1)] if x==y else [-(x+1),-(y+1)])
S=Solver(N,cl); t0=time.time(); r=S.solve(lim)
out=dict(k=k,sym=sym,vars=N,clauses=len(cl),result=r,conflicts=S.conflicts,secs=round(time.time()-t0,1))
if r:
    m=S.model(); B=[V[i] for i in range(N) if m[rep[i]]]
    # independent verification
    Bs=set(map(tuple,B))
    ok1=all(any(V[x] in Bs for x in st) for st in stars)
    ok2=all(sum(V[x] in Bs for x in g)<=1 for g in cliques)
    out.update(verified=ok1 and ok2,B=B)
print(json.dumps(out))
