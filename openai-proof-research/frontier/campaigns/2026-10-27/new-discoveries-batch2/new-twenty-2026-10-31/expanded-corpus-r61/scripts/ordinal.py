# Diagnostic search for Conjecture 7.4 (arXiv:2412.17391): weak orders on pairs of [n] whose identity
# enumeration has the majorization property, tested for line-embeddability by LP.
import itertools, sys, numpy as np
from scipy.optimize import linprog
n=int(sys.argv[1]); ties=sys.argv[2]=='ties' if len(sys.argv)>2 else False
P=list(itertools.combinations(range(n),2)); idx={p:i for i,p in enumerate(P)}
def chains(a,b):
    inner=list(range(a+1,b)); out=[]
    for r in range(len(inner)+1):
        for S in itertools.combinations(inner,r):
            pts=[a,*S,b]; out.append([idx[(pts[t],pts[t+1])] for t in range(len(pts)-1)])
    return out
CH=[(a,b,c) for (a,b) in P for c in chains(a,b)]
def majorization(rank):  # rank[pair]=class; diagonal = -1
    for (a,b,c) in CH:
        rc=sorted((rank[x] for x in c),reverse=True)
        for (e,f,d) in CH:
            rd=sorted((rank[x] for x in d),reverse=True); k=max(len(rc),len(rd))
            L=rc+[-1]*(k-len(rc)); R=rd+[-1]*(k-len(rd))
            if all(l<=r for l,r in zip(L,R)):
                lhs,rhs=rank[idx[(a,b)]],rank[idx[(e,f)]]
                if L==R:
                    if lhs!=rhs: return False
                elif not lhs<rhs: return False
    return True
def embeddable(rank):
    for perm in itertools.permutations(range(n)):
        if perm[0]>perm[-1]: continue
        pos={v:i for i,v in enumerate(perm)}
        def vec(p):
            a,b=sorted((pos[p[0]],pos[p[1]])); v=np.zeros(n-1); v[a:b]=1; return v
        cls=sorted(set(rank)); Aub=[];bub=[];Aeq=[];beq=[]
        groups=[[p for p in P if rank[idx[p]]==c] for c in cls]
        for g in groups:
            for p in g[1:]: Aeq.append(vec(p)-vec(g[0])); beq.append(0)
        for g,h in zip(groups,groups[1:]):
            Aub.append(vec(g[0])-vec(h[0])); bub.append(-1)
        res=linprog(np.zeros(n-1),A_ub=np.array(Aub) if Aub else None,b_ub=bub if bub else None,
                    A_eq=np.array(Aeq) if Aeq else None,b_eq=beq if beq else None,bounds=[(1,None)]*(n-1),method='highs')
        if res.status==0: return True
    return False
# containment poset: interval (a,b) strictly inside (c,d) must have smaller rank
below={p:[q for q in P if q!=p and p[0]<=q[0] and q[1]<=p[1]] for p in P}
count=0; maj=0; bad=[]
def extend(order,remaining):
    global count,maj
    if not remaining:
        count+=1; rank=[0]*len(P)
        for r,p in enumerate(order): rank[idx[p]]=r
        if majorization(rank):
            maj+=1
            if not embeddable(rank): bad.append(list(order)); print('COUNTEREXAMPLE',order,flush=True)
        return
    for p in list(remaining):
        if all(q in order for q in below[p]):
            remaining.remove(p); order.append(p); extend(order,remaining); order.pop(); remaining.add(p)
extend([],set(P))
print('n',n,'linear extensions',count,'majorization',maj,'non-embeddable',len(bad))
