# Structured search for Conjecture 4.7 (arXiv 2001.07925) counterexamples among bi-circulant graphs over Z_m:
# V = Z_m x {0,1}; (i,0)~(i+s,0), s in S0; (i,1)~(i+s,1), s in S1; (i,0)~(i+t,1), t in T (S0,S1 symmetric, 0 notin S0,S1).
# Regularity needs |S0| = |S1|. WLOG 0 in T (relabel the second orbit). Base points: (0,0) and (0,1) (all others equivalent
# under the rotation automorphism). Tests (S1), (S2) and the hypergroup axioms exactly via check() of hypergroup_search.py.
import sys, json, time, itertools
exec(open(sys.path[0]+'/hypergroup_search.py').read().split('t=time.time(); tot=0')[0])
mmin,mmax,maxS,maxT,BUDGET=map(int,sys.argv[1:6])
def symsets(m,maxsize):
    reps=[s for s in range(1,m//2+1)]
    out=[]
    for k in range(0,maxsize+1):
        for c in itertools.combinations(reps,k):
            S=set()
            for s in c: S|={s%m,(-s)%m}
            if len(S)<=maxsize: out.append(frozenset(S))
    return sorted(set(out),key=lambda S:(len(S),sorted(S)))
t0=time.time(); graphs=0; pointed=0; nondrg=0; bad=[]; timed=False; per_m={}
for m in range(mmin,mmax+1):
    ss=symsets(m,maxS)
    for T_rest in itertools.chain.from_iterable(itertools.combinations(range(1,m),k) for k in range(0,maxT)):
        T=(0,)+T_rest
        for S0 in ss:
            for S1 in ss:
                if len(S1)!=len(S0): continue
                if time.time()-t0>BUDGET: timed=True; break
                n=2*m; adj=[[] for _ in range(n)]
                for i in range(m):
                    for s in S0: adj[i].append((i+s)%m)
                    for s in S1: adj[m+i].append(m+(i+s)%m)
                    for t in T: adj[i].append(m+(i+t)%m); adj[m+(i+t)%m].append(i)
                if len({len(a) for a in adj})!=1 or len(adj[0])<2: continue
                D=dist_all(n,adj)
                if any(x<0 for x in D[0]): continue
                graphs+=1
                for v0 in (0,m):
                    res=check(n,adj,v0,D)
                    if res is None: continue
                    pointed+=1
                    # distance-regular?
                    tab={}; drg=True
                    for x in range(n):
                        for y in range(n):
                            prof=tuple(sorted((D[x][w],D[y][w]) for w in range(n)))
                            if tab.setdefault(D[x][y],prof)!=prof: drg=False; break
                        if not drg: break
                    if not drg: nondrg+=1
                    if not (res[0] and res[1]): bad.append({'m':m,'S0':sorted(S0),'S1':sorted(S1),'T':list(T),'v0':v0,'commutative':res[0],'associative':res[1]})
            if timed: break
        if timed: break
    per_m[m]=(graphs,pointed,nondrg)
    if timed: break
print(json.dumps({'m_range':[mmin,mmax],'max_S':maxS,'max_T':maxT,'complete':not timed,'last_m':m,'regular_connected_bicirculants':graphs,'pointed_S1S2':pointed,'pointed_S1S2_nonDRG':nondrg,'num_counterexamples':len(bad),'counterexamples':bad[:5],'secs':round(time.time()-t0,1)}))
