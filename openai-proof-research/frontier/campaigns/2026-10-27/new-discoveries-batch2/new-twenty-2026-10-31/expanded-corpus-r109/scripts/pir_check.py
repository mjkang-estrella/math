# MathDB 338214 sanity check (diagnostic): for random small codes over GF(2)/GF(3), compare
# (5) d_s >= n s / k (generalized Hamming weights by brute force over subcodes) with
# existence of a rational uniform base cover (LP over information sets), as predicted by Edmonds' theorem.
import itertools, random, json, numpy as np
from scipy.optimize import linprog
def rank(M,q):
    M=[list(r) for r in M]; r=0; cols=len(M[0]) if M else 0
    for c in range(cols):
        piv=next((i for i in range(r,len(M)) if M[i][c]%q),None)
        if piv is None: continue
        M[r],M[piv]=M[piv],M[r]; inv=pow(M[r][c],q-2,q); M[r]=[x*inv%q for x in M[r]]
        for i in range(len(M)):
            if i!=r and M[i][c]%q: f=M[i][c]; M[i]=[(a-f*b)%q for a,b in zip(M[i],M[r])]
        r+=1
    return r
def colrank(G,S,q): return rank([[G[i][j] for j in S] for i in range(len(G))],q) if S else 0
def ghw(G,n,k,q):
    # d_s = n - max{|Z| : k - r(Z) >= s} (Wei duality); computed directly from subsets
    best={s:n+1 for s in range(1,k+1)}
    for z in range(n+1):
        for Z in itertools.combinations(range(n),z):
            s=k-colrank(G,Z,q)
            for t in range(1,s+1): best[t]=min(best[t],n-z)
    return best
def lp_cover(G,n,k,q):
    bases=[B for B in itertools.combinations(range(n),k) if colrank(G,B,q)==k]
    A=np.zeros((n,len(bases)))
    for b,B in enumerate(bases):
        for j in B: A[j,b]=1
    res=linprog(np.zeros(len(bases)),A_eq=np.vstack([A,np.ones(len(bases))]),b_eq=np.concatenate([np.full(n,k/n),[1]]),bounds=(0,None),method='highs')
    return res.status==0
rng=random.Random(109); stats={'agree':0,'disagree':[]}
for t in range(300):
    q=rng.choice([2,3]); n=rng.randint(3,8); k=rng.randint(1,n-1)
    G=[[rng.randrange(q) for _ in range(n)] for _ in range(k)]
    if rank(G,q)<k: continue
    d=ghw(G,n,k,q); cond=all(d[s]*k>=n*s for s in d)
    lp=lp_cover(G,n,k,q)
    stats['cond_true']=stats.get('cond_true',0)+int(cond)
    if cond==lp: stats['agree']+=1
    else: stats['disagree'].append({'q':q,'G':G,'cond':cond,'lp':lp})
print(stats['agree'],len(stats['disagree']),'cond_true',stats.get('cond_true'))
json.dump(stats,open('outputs/pir-check.json','w'),indent=1)
