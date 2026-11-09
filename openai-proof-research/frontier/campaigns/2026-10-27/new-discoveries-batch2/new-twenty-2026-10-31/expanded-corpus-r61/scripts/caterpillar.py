# Diagnostic search: caterpillars, r>=3, maximum r-centers vs neighbour degree.
import itertools,sys
def cat(t):  # t[i] = number of pendant leaves on spine vertex i
    k=len(t); adj={i:set() for i in range(k)}; n=k
    for i in range(k-1): adj[i].add(i+1); adj[i+1].add(i)
    for i,c in enumerate(t):
        for _ in range(c): adj[n]={i}; adj[i].add(n); n+=1
    return adj
def indep_counts_containing(adj):
    n=len(adj); nb=[0]*n
    for v in adj:
        for u in adj[v]: nb[v]|=1<<u
    # count independent sets by size containing each vertex via simple enumeration (small n)
    res=[[0]*(n+1) for _ in range(n)]
    def rec(i,chosen,forb,size):
        if i==n:
            for v in range(n):
                if chosen>>v&1: res[v][size]+=1
            return
        rec(i+1,chosen,forb,size)
        if not forb>>i&1: rec(i+1,chosen|1<<i,forb|nb[i],size+1)
    rec(0,0,0,0); return res,nb
found=[]
for k in range(1,7):
  for t in itertools.product(range(0,4),repeat=k):
    if k>=2 and (t[0]==0 or t[-1]==0): continue  # ends of spine carry leaves (canonical-ish)
    adj=cat(t); n=len(adj)
    if n>16: continue
    res,nb=indep_counts_containing(adj); deg=[len(adj[v]) for v in range(n)]; D=max(deg)
    for r in range(3,n+1):
        vals=[res[v][r] for v in range(n)]; M=max(vals)
        if M==0: break
        cent=[v for v in range(n) if vals[v]==M]
        bad=[z for z in cent if not any(deg[u]==D for u in adj[z])]
        leafbad=[z for z in bad if deg[z]==1]
        if leafbad:
            exist_ok=any(any(deg[u]==D for u in adj[z]) for z in cent)
            found.append((n,t,r,M,leafbad,exist_ok))
found.sort()
print(len(found))
for f in found[:40]: print(f)
print('exist-fail', [f for f in found if not f[5]][:20])
# strongest reading: every leaf adjacent to a max-degree vertex is a maximum r-center?
