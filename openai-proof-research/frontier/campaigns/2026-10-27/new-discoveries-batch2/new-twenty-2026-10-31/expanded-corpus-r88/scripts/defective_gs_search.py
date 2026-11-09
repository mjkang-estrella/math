# Exhaustive small search for counterexamples to Aboulker-Aubian-Huang Conjecture 5.4 (arXiv 2201.11548):
# loopless multigraph G, odd d: chi'_d(G) <= max{Gamma_d(G), ceil((Delta+1)/d)},
# Gamma_d = max_X ceil(|E(G[X])| / floor(d|X|/2)) over X with floor(d|X|/2)>0.
# Prefilter with the proved bound chi'_d <= ceil((3Delta-1)/(3d-1)) (Theorem 1.1 of the source);
# then decide (B,d)-colourability exactly by an integer program (scipy/HiGHS) with B = conjectured bound.
import sys, itertools, json, time
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
n=int(sys.argv[1]); M=int(sys.argv[2]); d=int(sys.argv[3])
SHARD=int(sys.argv[4]) if len(sys.argv)>4 else None  # if given: multiplicity of pair (0,1) fixed to SHARD and it is a maximum multiplicity (WLOG by relabelling)
pairs=list(itertools.combinations(range(n),2))
cdiv=lambda a,b: -(-a//b)
def colourable(mult,k):
    E=[(p,mu) for p,mu in zip(pairs,mult) if mu>0]
    nv=len(E)*k; idx=lambda e,c: e*k+c
    A=[];lb=[];ub=[]
    for e,(p,mu) in enumerate(E):
        row=np.zeros(nv); row[[idx(e,c) for c in range(k)]]=1; A.append(row); lb.append(mu); ub.append(mu)
    for v in range(n):
        for c in range(k):
            row=np.zeros(nv)
            for e,(p,mu) in enumerate(E):
                if v in p: row[idx(e,c)]=1
            A.append(row); lb.append(0); ub.append(d)
    # symmetry breaking: colour loads nonincreasing on the first parallel class
    hi=np.array([mu for (p,mu) in E for c in range(k)],dtype=float)
    res=milp(c=np.zeros(nv),constraints=LinearConstraint(np.array(A),lb,ub),integrality=np.ones(nv),bounds=Bounds(0,hi),options={'time_limit':20})
    if res.status==0: return True
    if res.status==2: return False
    raise RuntimeError(('milp status',res.status,mult,k))
def canon(mult):
    best=None
    for perm in itertools.permutations(range(n)):
        m={}
        for (a,b),mu in zip(pairs,mult):
            x,y=sorted((perm[a],perm[b])); m[(x,y)]=mu
        t=tuple(m[p] for p in pairs)
        if best is None or t>best: best=t
    return best
subsets=[s for r in range(1,n+1) for s in itertools.combinations(range(n),r) if (d*r)//2>0]
t=time.time(); seen=set(); tested=0; ilps=0; cex=[]; tight=0
for mult in (itertools.product(range(M+1),repeat=len(pairs)) if SHARD is None else ((SHARD,)+r for r in itertools.product(range(SHARD+1),repeat=len(pairs)-1))):
    tested+=1
    deg=[sum(mu for p,mu in zip(pairs,mult) if v in p) for v in range(n)]
    D=max(deg)
    if D==0: continue
    gam=max(cdiv(sum(mu for p,mu in zip(pairs,mult) if p[0] in s and p[1] in s),(d*len(s))//2) for s in subsets)
    B=max(gam,cdiv(D+1,d))
    if cdiv(3*D-1,3*d-1)<=B: continue
    c=canon(mult)
    if c in seen: continue
    seen.add(c)
    ilps+=1
    if not colourable(mult,B):
        cex.append({'mult':dict(zip(map(str,pairs),mult)),'Delta':D,'Gamma_d':gam,'bound':B})
    else: tight+=1
print(json.dumps({'shard_max_mult_on_pair01':SHARD,'n':n,'max_multiplicity':M,'d':d,'labelled_multigraphs':tested,'ilp_checked_iso_classes':ilps,'counterexamples':cex[:10],'num_counterexamples':len(cex),'secs':time.time()-t}))
