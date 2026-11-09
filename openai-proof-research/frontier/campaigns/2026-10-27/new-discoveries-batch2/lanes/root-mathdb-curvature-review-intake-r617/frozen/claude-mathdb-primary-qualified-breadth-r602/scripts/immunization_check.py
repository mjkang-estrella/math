# 338408 / Dourado-Ehard-Penso-Rautenbach Conjecture 1.3 (arXiv:1802.03754v1): exhaustive small-graph check.
# For every graph G on n<=NMAX vertices (isomorphism-deduplicated) and every 0<=b<=2m: is there a matching M with
# tau_M(V)<=b and vacc(G,0,d_G,b) <= 2*dyn(G,tau_M)?  vacc = max dyn(G,iota) over integer 0<=iota<=d_G, sum iota = b.
# hull: iteratively add u with |H cap N(u)| >= tau(u); dyn = min |D| with hull(D)=V.
import itertools,json,sys
NMAX=int(sys.argv[1])
def canon(n,E):
    best=None
    for p in itertools.permutations(range(n)):
        c=tuple(sorted(tuple(sorted((p[a],p[b]))) for a,b in E))
        if best is None or c<best: best=c
    return best
def run(n,E):
    N=[0]*n
    for a,b in E: N[a]|=1<<b; N[b]|=1<<a
    deg=[bin(x).count('1') for x in N]; full=(1<<n)-1
    subs=sorted(range(1<<n),key=lambda s:bin(s).count('1'))
    def dyn(t):
        for D in subs:
            H=D; ch=True
            while ch:
                ch=False
                for u in range(n):
                    if not H>>u&1 and bin(H&N[u]).count('1')>=t[u]: H|=1<<u; ch=True
            if H==full: return bin(D).count('1')
    cache={}
    def dy(t):
        if t not in cache: cache[t]=dyn(t)
        return cache[t]
    m=len(E); vacc={}
    for t in itertools.product(*[range(d+1) for d in deg]):
        s=sum(t); v=dy(t)
        if v>vacc.get(s,-1): vacc[s]=v
    # matchings
    Ms=[()]
    for r in range(1,n//2+1):
        for c in itertools.combinations(E,r):
            vs=[x for e in c for x in e]
            if len(set(vs))==len(vs): Ms.append(c)
    fails=[]
    for b in range(0,2*m+1):
        ok=False
        for M in Ms:
            cov={x for e in M for x in e}
            t=tuple(deg[u] if u in cov else 0 for u in range(n))
            if sum(t)<=b and vacc[b]<=2*dy(t): ok=True; break
        if not ok:
            aff=any(M and sum(deg[u] for e in M for u in e)<=b for M in Ms)
            fails.append([b,vacc[b],'nonboundary' if aff else 'boundary'])
    return fails
seen=set(); stats={'graphs':0}; out=[]
import random
if len(sys.argv)>2:
    # random labelled graphs on n=NMAX vertices, no dedupe; count = argv[2]
    rng=random.Random(int(sys.argv[3])); n=NMAX; pairs=list(itertools.combinations(range(n),2))
    for _ in range(int(sys.argv[2])):
        p=rng.choice([0.3,0.5,0.7]); E=[e for e in pairs if rng.random()<p]
        stats['graphs']+=1; f=run(n,E)
        if any(x[2]=='nonboundary' for x in f): out.append({'n':n,'E':E,'fails':f})
        elif f: stats['boundary_only']=stats.get('boundary_only',0)+1
    print(json.dumps({'stats':stats,'nonboundary_counterexamples':out[:5],'num':len(out)})); sys.exit(0)
for n in range(1,NMAX+1):
    pairs=list(itertools.combinations(range(n),2))
    for mask in range(1<<len(pairs)):
        E=[pairs[i] for i in range(len(pairs)) if mask>>i&1]
        c=canon(n,E)
        if (n,c) in seen: continue
        seen.add((n,c)); stats['graphs']+=1
        f=run(n,list(c))
        if f: out.append({'n':n,'E':c,'failing_b':f})
    stats['n%d'%n]=stats['graphs']
print(json.dumps({'stats':stats,'counterexamples':out[:10],'num_counterexamples':len(out)}))
