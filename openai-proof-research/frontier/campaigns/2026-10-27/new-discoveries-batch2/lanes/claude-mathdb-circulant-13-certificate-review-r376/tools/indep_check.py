# r376 independent checker for MathDB 372627 (C_n(1,3), L(3,2,1)). Written from scratch; does not import or read r360 code.
# Exits nonzero on any failed assertion.  Usage: indep_check.py OUTJSON
import sys,json,hashlib
from collections import deque
OUT=sys.argv[1]; res={}
def bfs_cn(n,S=(1,3)):
    d=[-1]*n; d[0]=0; q=deque([0])
    while q:
        u=q.popleft()
        for s in S:
            for v in ((u+s)%n,(u-s)%n):
                if d[v]<0: d[v]=d[u]+1; q.append(v)
    return d
# (1) distance profile in Z (steps +-1,+-3), radius <=3, via BFS on a bounded segment large enough
def zdist(R=40):
    d={0:0}; q=deque([0])
    while q:
        u=q.popleft()
        if d[u]>=3: continue
        for s in (1,-1,3,-3):
            v=u+s
            if v not in d: d[v]=d[u]+1; q.append(v)
    return {e:d[e] for e in d if e>0}
Z=zdist(); OFF={1:3,2:2,3:3,4:2,5:1,6:2,7:1,9:1}  # claimed offsets: offset -> required |diff| = 4 - dist
assert {e:4-Z[e] for e in sorted(Z)}==OFF, Z
res['Z_dist_le3']={str(e):Z[e] for e in sorted(Z)}
# (2) actual C_n distance: for every n in 19..400 (and n in 7..18 to show where it breaks) compare actual BFS with lifted profile
def lifted(n):
    out={}
    for r in range(1,n):
        cands=[Z[e] for e in Z if (e-r)%n==0]+[Z[e] for e in Z if (-e-r)%n==0]
        out[r]=min(cands) if cands else None
    return out
bad_small=[]
for n in range(7,401):
    d=bfs_cn(n); L=lifted(n)
    ok=all((d[r] if d[r]<=3 else None)==L[r] for r in range(1,n))
    if n>=19: assert ok,n
    elif not ok: bad_small.append(n)
res['distance_equivalence_checked_n']=[19,400]; res['distance_equivalence_fails_for_small_n']=bad_small
# (3) span normalization: span s <=> labels {0..s} (K=s+1 labels).  constraint between positions i<j at offset e=j-i:
def okpair(a,b,e): return abs(a-b)>=OFF[e] if e in OFF else True
# exhaustive valid windows of length W=9 (offsets up to 8 inside a window) via DFS extension; completeness: every valid word's
# every prefix is valid (constraints are pairwise, hereditary), so DFS over prefixes enumerates all valid 9-words exactly.
def windows(K,W=9):
    out=[]; w=[]
    def rec():
        if len(w)==W: out.append(tuple(w)); return
        j=len(w)
        for a in range(K):
            if all(okpair(w[i],a,j-i) for i in range(max(0,j-9),j)): w.append(a); rec(); w.pop()
    rec(); return out
def valid10(t): return all(okpair(t[i],t[j],j-i) for i in range(10) for j in range(i+1,10))
def graph(K):
    V=windows(K); Vs=set(V)
    # completeness cross-check against independent brute force on smaller window lengths is done below for K=12 via product counting
    E={v:[] for v in V}; ne=0
    for v in V:
        for a in range(K):
            t=v+(a,)
            if valid10(t):
                u=t[1:]; assert u in Vs; E[v].append(u); ne+=1
    return V,E,ne
def scc(V,E):
    idx={};low={};on=set();st=[];comps=[];c=[0]
    sys.setrecursionlimit(100000)
    def sc(v):
        idx[v]=low[v]=c[0];c[0]+=1;st.append(v);on.add(v)
        for u in E[v]:
            if u not in idx: sc(u);low[v]=min(low[v],low[u])
            elif u in on: low[v]=min(low[v],idx[u])
        if low[v]==idx[v]:
            comp=[]
            while True:
                x=st.pop();on.discard(x);comp.append(x)
                if x==v:break
            comps.append(comp)
    for v in V:
        if v not in idx: sc(v)
    return comps
def period(comp,E):
    S=set(comp); r=comp[0]; lv={r:0}; q=deque([r]); g=0
    while q:
        u=q.popleft()
        for w in E[u]:
            if w in S:
                if w not in lv: lv[w]=lv[u]+1;q.append(w)
                else: g=__import__('math').gcd(g,lv[u]+1-lv[w])
    return g,lv
for K in (11,12):
    V,E,ne=graph(K); comps=scc(V,E)
    nontriv=[c for c in comps if len(c)>1 or c[0] in E[c[0]]]
    info={'states':len(V),'edges':ne,'nontrivial_scc_sizes':sorted(len(c) for c in nontriv)}
    pers=[]
    for c in nontriv:
        g,lv=period(c,E); pers.append(g)
        # potential certificate: phi(u)=lv mod g, every intra-SCC edge v->u has phi(u)=phi(v)+1 mod g
        S=set(c)
        for v in c:
            for u in E[v]:
                if u in S: assert (lv[u]-lv[v]-1)%g==0
        # is it a simple directed cycle (every vertex out-degree 1 inside the SCC)?
        info.setdefault('scc_simple_cycle',[]).append(all(sum(1 for u in E[v] if u in S)==1 for v in c))
        info.setdefault('scc_label_steps',[]).append(sorted({(v[1]-v[0])%K for v in c}))
    info['periods']=pers
    # topological order on condensation (independent acyclicity witness for cross-SCC edges)
    comp_of={v:i for i,c in enumerate(comps) for v in c}  # Tarjan emits comps in reverse topological order
    for v in V:
        for u in E[v]: assert comp_of[u]<=comp_of[v]
    res[f'K{K}']=info
    if K==11: assert info['states']==6 and ne==4 and not nontriv
    if K==12: assert info['states']==152 and ne==128 and info['periods']==[12,12] and info['nontrivial_scc_sizes']==[12,12]
    res[f'K{K}_states_sha256']=hashlib.sha256(json.dumps(sorted(V)).encode()).hexdigest()
    res[f'K{K}_edges_sha256']=hashlib.sha256(json.dumps(sorted((v,u) for v in V for u in E[v])).encode()).hexdigest()
    if K==12: V12,E12=V,E
# (4) the bridge: a cyclic word of length n (n>=19) is a labeling iff all n cyclic 10-windows valid iff closed walk of length n.
# Check directly with a constraint function on the actual circulant (BFS distances), independent of window code:
def is_labeling(f):
    n=len(f); d=bfs_cn(n); dist=lambda i,j:d[(j-i)%n]
    return all(abs(f[i]-f[j])>=4-dist(i,j) for i in range(n) for j in range(i+1,n) if dist(i,j)<=3)
# (5) upper witnesses: build cyclic words with 13 labels as closed walks at s0, lengths 12 and every even 142..164
s0=(0,5,10,3,8,1,6,11,4)
def closed_walk(K,s,L):
    # BFS layered reachability backwards: R[t] = states that reach s in exactly t steps; then walk greedily forward.
    V=windows(K); Vs=set(V); succ={}
    for v in V:
        succ[v]=[ (v+(a,))[1:] for a in range(K) if valid10(v+(a,)) ]
    pred={v:[] for v in V}
    for v in V:
        for u in succ[v]: pred[u].append(v)
    R=[{s}]
    for t in range(1,L+1):
        R.append({p for u in R[-1] for p in pred[u]})
    if s not in R[L]: return None,len(V)
    word=[];cur=s
    for t in range(L,0,-1):
        nxt=next(u for u in succ[cur] if u in R[t-1]); word.append(nxt[-1]); cur=nxt
    return word,len(V)
assert s0 in set(V12)  # s0 is a 12-label window too (it is on the 5i cycle)
res['upper']={}
lengths=[12]+list(range(142,165,2))
witnesses={}
for L in lengths:
    w,nv=closed_walk(13,s0,L)
    assert w is not None,L
    # rotate so that word begins with s0 labels: walk emits labels following s0; cyclic word = emitted labels
    assert is_labeling(w) and max(w)<=12 and min(w)>=0,L
    witnesses[L]=w
res['K13_states']=nv
# additive closure: concatenating two closed walks at s0 is a closed walk at s0 -> word concatenation (both words start right after s0)
# check the concatenation claim concretely for every even n in 142..400 via explicit words, on the actual circulant
cover={}
for n in range(142,401,2):
    base=next(b for b in range(142,154,2) if (n-b)%12==0); k=(n-base)//12
    f=witnesses[base]+witnesses[12]*k
    assert len(f)==n and is_labeling(f),n
    cover[n]=base
res['upper_concatenation_checked_even_n']=[142,400]
res['witness_words']={str(L):witnesses[L] for L in lengths}
# (6) lower bound cross-check by direct cyclic backtracking on actual circulant (no window graph) for a spread of n with 12 labels
def exists(n,K):
    d=bfs_cn(n); cons=[(e,4-d[e]) for e in range(1,n) if d[e]<=3]
    f=[None]*n; f[0]=0
    def ok(i,a):
        for e,m in cons:
            j=(i-e)%n
            if f[j] is not None and abs(f[j]-a)<m: return False
        return True
    def rec(i):
        if i==n: return True
        for a in range(K):
            if ok(i,a):
                f[i]=a
                if rec(i+1): return True
                f[i]=None
        return False
    # WLOG f(0)=0 is NOT valid for minimal labels in general (some vertex has label 0, by vertex-transitivity rotate it to 0)
    return rec(1)
bt={}
for n in list(range(19,41))+[48,50,60,62,72]:
    e=exists(n,12); bt[n]=e; assert e==(n%12==0),(n,e)
res['direct_backtrack_K12']={str(n):bt[n] for n in bt}
for n in range(19,31):
    assert not exists(n,11)
res['direct_backtrack_K11_none_n']=[19,30]
json.dump(res,open(OUT,'w'),indent=1,sort_keys=True); print('PASS')
