# Exact gadget excess for the Harmonic index - radius conjecture in the path-like regime.
# G = (long path) - X - (long path)  [inline, terminals a,b; a=b allowed]  or  X - (long path) [end, root a].
# Delta(G)=H(G)-r(G) = sum of excesses - 1/6 when the main-line length S is odd; counterexample iff excess < 1/6.
import sys, json, pathlib
from fractions import Fraction as F
reps=json.loads(pathlib.Path(sys.argv[1]).read_text()); nmin=int(sys.argv[2]); nmax=int(sys.argv[3])
def bfs(n,adj,s):
    d=[-1]*n; d[s]=0; q=[s]
    for v in q:
        for u in adj[v]:
            if d[u]<0: d[u]=d[v]+1; q.append(u)
    return d
best_end=[]; best_in=[]
for n in range(nmin,nmax+1):
    for E in reps[str(n)]:
        adj=[[] for _ in range(n)]
        for i,j in E: adj[i].append(j); adj[j].append(i)
        D=[bfs(n,adj,s) for s in range(n)]
        if any(x<0 for x in D[0]): continue
        deg=[len(a) for a in adj]
        ispath = (len(E)==n-1 and max(deg)<=2)
        for a in range(n):
            dg=deg[:]; dg[a]+=1
            Hin=sum(F(2,dg[i]+dg[j]) for i,j in E)
            e=F(2,deg[a]+3)+Hin-F(max(D[a]),2)-F(2,3)
            if not (ispath and deg[a]<=1): best_end.append((e,n,E,a))
        for a in range(n):
            for b in range(a,n):
                dg=deg[:]; dg[a]+=1; dg[b]+=1
                Hin=sum(F(2,dg[i]+dg[j]) for i,j in E)
                e=F(2,dg[a]+2)+F(2,dg[b]+2)+Hin-F(D[a][b],2)-1
                trivial = ispath and ((a!=b and deg[a]<=1 and deg[b]<=1) or n==1)
                if not trivial: best_in.append((e,n,E,a,b))
    best_end.sort(key=lambda t:t[0]); best_in.sort(key=lambda t:t[0])
    best_end=best_end[:15]; best_in=best_in[:15]
    if best_end and best_in: print('n<=',n,'min end excess',best_end[0][0],float(best_end[0][0]),'min inline excess',best_in[0][0],float(best_in[0][0]),flush=True)
res={'end':[(str(e),n,E,a) for e,n,E,a in best_end],'inline':[(str(e),n,E,a,b) for e,n,E,a,b in best_in]}
pathlib.Path(sys.argv[4]).write_text(json.dumps(res,indent=0))
for t in best_end[:8]: print('END',t[0],t[1:])
for t in best_in[:8]: print('IN',t[0],t[1:])
