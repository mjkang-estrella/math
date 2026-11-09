# 345726: random arc-minimal 3-arc-strong digraphs with independence number exactly 2;
# test every (s,t) for arc-disjoint out-branching B_s^+ and in-branching B_t^-.
import sys, random, itertools, time
n=int(sys.argv[1]); trials=int(sys.argv[2]); seed=int(sys.argv[3]); tlimit=float(sys.argv[4]); K=int(sys.argv[5]) if len(sys.argv)>5 else 3
random.seed(seed)
def alpha_le2(A):
    adj=[[A[i][j] or A[j][i] for j in range(n)] for i in range(n)]
    for a,b,c in itertools.combinations(range(n),3):
        if not adj[a][b] and not adj[a][c] and not adj[b][c]: return False
    return True
def alpha_eq2(A):
    adj=[[A[i][j] or A[j][i] for j in range(n)] for i in range(n)]
    return alpha_le2(A) and any(not adj[a][b] for a,b in itertools.combinations(range(n),2))
def maxflow(A,s,t,cap=None):
    cap=K if cap is None else cap
    # unit capacities, count up to cap edge-disjoint paths
    R=[[1 if A[i][j] else 0 for j in range(n)] for i in range(n)]; f=0
    while f<cap:
        prev=[-1]*n; prev[s]=s; q=[s]
        while q and prev[t]<0:
            u=q.pop()
            for v in range(n):
                if R[u][v]>0 and prev[v]<0: prev[v]=u; q.append(v)
        if prev[t]<0: break
        v=t
        while v!=s: u=prev[v]; R[u][v]-=1; R[v][u]+=1; v=u
        f+=1
    return f
def arc_strong3(A):
    return all(maxflow(A,0,v)>=K and maxflow(A,v,0)>=K for v in range(1,n))
def reaches_all_to(A,t,banned):
    seen={t}; st=[t]
    while st:
        v=st.pop()
        for u in range(n):
            if A[u][v] and (u,v) not in banned and u not in seen: seen.add(u); st.append(u)
    return len(seen)==n
def good_pair(A,s,t):
    # complete enumeration of out-branchings rooted at s: a parent p(v) in N^-(v) for each v != s,
    # such that following parents from every v reaches s (acyclic); then test the complement
    # for an in-branching to t (every vertex reaches t using unused arcs).
    others=[v for v in range(n) if v!=s]
    ins={v:[u for u in range(n) if A[u][v]] for v in others}
    par={}
    def ok_partial(v):
        # follow parents from v; detect cycle among assigned vertices
        seen=set(); x=v
        while x!=s and x in par:
            if x in seen: return False
            seen.add(x); x=par[x]
        return True
    def rec(k):
        if k==len(others):
            used={(par[v],v) for v in others}
            return reaches_all_to(A,t,used)
        v=others[k]
        for u in ins[v]:
            par[v]=u
            if ok_partial(v) and rec(k+1): return True
        del par[v]
        return False
    return rec(0)
found=0; tested=0; t0=time.time()
for tr in range(trials):
    if time.time()-t0>tlimit: break
    A=[[1 if i!=j and random.random()<0.85 else 0 for j in range(n)] for i in range(n)]
    if not (alpha_le2(A) and arc_strong3(A)): continue
    arcs=[(i,j) for i in range(n) for j in range(n) if A[i][j]]; random.shuffle(arcs)
    for (i,j) in arcs:
        A[i][j]=0
        if not (alpha_le2(A) and arc_strong3(A)): A[i][j]=1
    if not alpha_eq2(A): continue
    tested+=1
    for s in range(n):
        for t in range(n):
            if not good_pair(A,s,t):
                found+=1; print('NO GOOD PAIR', s,t, [(i,j) for i in range(n) for j in range(n) if A[i][j]],flush=True)
print('n',n,'K',K,'seed',seed,'minimal digraphs tested',tested,'counterexamples',found,'time',round(time.time()-t0,1))
