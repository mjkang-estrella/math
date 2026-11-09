# Diagnostic: incremental search over weak orders on pairs of [n] (classes built bottom-up),
# pruning by majorization constraints as soon as all involved pairs are ranked.
import itertools, sys, time, numpy as np
from scipy.optimize import linprog
n=int(sys.argv[1]); allow_ties=(sys.argv[2]=='ties'); T0=time.time(); LIMIT=float(sys.argv[3])
P=list(itertools.combinations(range(n),2)); idx={p:i for i,p in enumerate(P)}; m=len(P)
def chains(a,b):
    inner=list(range(a+1,b)); out=[]
    for r in range(len(inner)+1):
        for S in itertools.combinations(inner,r):
            pts=[a,*S,b]; out.append([idx[(pts[t],pts[t+1])] for t in range(len(pts)-1)])
    return out
CH=[(idx[(a,b)],c) for (a,b) in P for c in chains(a,b)]
CONS=[]
for (e1,c) in CH:
    for (e2,d) in CH:
        if (e1,tuple(c))==(e2,tuple(d)): continue
        CONS.append((e1,tuple(c),e2,tuple(d),frozenset(c)|frozenset(d)|{e1,e2}))
by_pair=[[] for _ in range(m)]
for k,cn in enumerate(CONS):
    for q in cn[4]: by_pair[q].append(k)
def ok(cn,rank):
    e1,c,e2,d,_=cn
    rc=sorted((rank[x] for x in c),reverse=True); rd=sorted((rank[x] for x in d),reverse=True)
    k=max(len(rc),len(rd)); L=rc+[-1]*(k-len(rc)); R=rd+[-1]*(k-len(rd))
    if all(l<=r for l,r in zip(L,R)):
        if L==R: return rank[e1]==rank[e2]
        return rank[e1]<rank[e2]
    return True
def embeddable(rank):
    cls=sorted(set(rank)); groups=[[P[i] for i in range(m) if rank[i]==c] for c in cls]
    for perm in itertools.permutations(range(n)):
        if perm[0]>perm[-1]: continue
        pos={v:i for i,v in enumerate(perm)}
        def vec(p):
            a,b=sorted((pos[p[0]],pos[p[1]])); v=np.zeros(n-1); v[a:b]=1; return v
        Aeq=[vec(p)-vec(g[0]) for g in groups for p in g[1:]]
        Aub=[vec(g[0])-vec(h[0]) for g,h in zip(groups,groups[1:])]
        res=linprog(np.zeros(n-1),A_ub=np.array(Aub) if Aub else None,b_ub=[-1]*len(Aub) if Aub else None,
            A_eq=np.array(Aeq) if Aeq else None,b_eq=[0]*len(Aeq) if Aeq else None,bounds=[(1,None)]*(n-1),method='highs')
        if res.status==0: return True
    return False
below=[[idx[q] for q in P if q!=p and p[0]<=q[0] and q[1]<=p[1]] for p in P]
rank=[None]*m; stats=dict(complete=0,maj=0,bad=0,timeout=False); bad=[]
def check_new(newly):
    seen=set()
    for q in newly:
        for k in by_pair[q]:
            if k in seen: continue
            seen.add(k); cn=CONS[k]
            if all(rank[x] is not None for x in cn[4]) and not ok(cn,rank): return False
    return True
def rec(level,placed):
    if time.time()-T0>LIMIT: stats['timeout']=True; return
    if placed==m:
        stats['complete']+=1
        if not embeddable(rank):
            stats['bad']+=1; bad.append(list(rank)); print('COUNTEREXAMPLE',[(P[i],rank[i]) for i in range(m)],flush=True)
        return
    avail=[i for i in range(m) if rank[i] is None and all(rank[j] is not None for j in below[i])]
    sizes=range(1,len(avail)+1) if allow_ties else [1]
    for s in sizes:
        for S in itertools.combinations(avail,s):
            for i in S: rank[i]=level
            if check_new(S): rec(level+1,placed+s)
            for i in S: rank[i]=None
            if stats['timeout']: return
rec(0,0)
print('n',n,'ties',allow_ties,stats,'elapsed',round(time.time()-T0,1),flush=True)
