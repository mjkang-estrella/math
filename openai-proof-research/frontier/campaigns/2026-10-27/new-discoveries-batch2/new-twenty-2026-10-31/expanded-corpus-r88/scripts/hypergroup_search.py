# Exhaustive search for counterexamples to Endo--Mimura--Sawada Conjecture 4.7 (arXiv 2001.07925):
# a pointed graph (Gamma, v0) satisfying (S1) and (S2) produces a hypergroup, i.e. the Wildberger constants
#   p^k_{ij} = (1/|S_i(v0)|) sum_{v in S_i(v0)} |S_j(v) ∩ S_k(v0)| / |S_j(v)|      (source eq. (2.1))
# are commutative (p^k_{ij}=p^k_{ji}) and associative (sum_l p^l_{hi} p^k_{lj} = sum_l p^l_{ij} p^k_{hl})  (source §2.2).
# (S1): |S_i(.)| constant on V for each i in I(Gamma,v0); (S2): |S_i(.) ∩ S_j(v0)| constant on S_k(v0), i,j,k in I.
# Input: graph6 files of connected graphs (McKay catalogue). Exact rational arithmetic.
import sys, json, time
from fractions import Fraction as F
from collections import deque
def g6(line):
    s=line.strip(); data=[c-63 for c in s.encode()]
    n=data[0]; bits=[]
    for x in data[1:]:
        for b in range(5,-1,-1): bits.append((x>>b)&1)
    adj=[[] for _ in range(n)]; t=0
    for j in range(1,n):
        for i in range(j):
            if bits[t]: adj[i].append(j); adj[j].append(i)
            t+=1
    return n,adj
def dist_all(n,adj):
    D=[]
    for s in range(n):
        d=[-1]*n; d[s]=0; q=deque([s])
        while q:
            v=q.popleft()
            for w in adj[v]:
                if d[w]<0: d[w]=d[v]+1; q.append(w)
        D.append(d)
    return D
def check(n,adj,v0,D):
    I=sorted(set(D[v0])); 
    S=lambda i,v:[w for w in range(n) if D[v][w]==i]
    cnt={(i,v):sum(1 for w in range(n) if D[v][w]==i) for i in I for v in range(n)}
    for i in I:
        if len({cnt[(i,v)] for v in range(n)})!=1: return None   # S1 fails
    for k in I:
        Sk=S(k,v0)
        for i in I:
            for j in I:
                vals={sum(1 for w in range(n) if D[v][w]==i and D[v0][w]==j) for v in Sk}
                if len(vals)!=1: return None   # S2 fails
    p={}
    for i in I:
        Si=S(i,v0)
        for j in I:
            for k in I:
                p[(i,j,k)]=sum(F(sum(1 for w in range(n) if D[v][w]==j and D[v0][w]==k),cnt[(j,v)]) for v in Si)/len(Si)
    comm=all(p[(i,j,k)]==p[(j,i,k)] for i in I for j in I for k in I)
    assoc=all(sum(p[(h,i,l)]*p[(l,j,k)] for l in I)==sum(p[(i,j,l)]*p[(h,l,k)] for l in I) for h in I for i in I for j in I for k in I)
    return comm,assoc
t=time.time(); tot=0; reg=0; s1s2=0; dr_like=0; bad=[]; examples=[]
for path in sys.argv[1:]:
    for line in open(path,'rb'):
        line=line.decode().strip()
        if not line or line.startswith('>'): continue
        n,adj=g6(line); tot+=1
        degs={len(a) for a in adj}
        if len(degs)!=1: continue
        reg+=1; D=dist_all(n,adj)
        for v0 in range(n):
            r=check(n,adj,v0,D)
            if r is None: continue
            s1s2+=1
            if len(examples)<3: examples.append((line,v0))
            if not (r[0] and r[1]): bad.append({'g6':line,'v0':v0,'commutative':r[0],'associative':r[1]})
print(json.dumps({'files':sys.argv[1:],'graphs':tot,'regular_connected':reg,'pointed_graphs_with_S1_S2':s1s2,'counterexamples':bad[:10],'num_counterexamples':len(bad),'secs':round(time.time()-t,1)}))
