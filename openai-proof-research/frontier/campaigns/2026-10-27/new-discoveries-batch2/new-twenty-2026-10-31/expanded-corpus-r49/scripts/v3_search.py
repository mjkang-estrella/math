# MathDB 355701 (arXiv:2208.06912 Conj. after Thm 6.1): search symmetric v3 (n_3) combinatorial configurations
# with max pairwise-intersecting line set <= 4 and NO line 2-coloring free of monochromatic triangles.
# Triangle: three lines pairwise meeting in three distinct points (non-concurrent), per source Definition.
import sys, random, json, itertools, resource, time
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,)*2); cpu=int(sys.argv[3]); resource.setrlimit(resource.RLIMIT_CPU,(cpu,cpu))
def random_config(n,rng,tries=200):
    for _ in range(tries):
        deg=[0]*n; pairs=set(); lines=[]; ok=True
        for _l in range(n):
            # pick point with fewest remaining options first
            cand=[p for p in range(n) if deg[p]<3]
            p=min(cand,key=lambda x:(deg[x],rng.random()))
            opts=[(a,b) for a,b in itertools.combinations([x for x in cand if x!=p],2)
                  if (min(p,a),max(p,a)) not in pairs and (min(p,b),max(p,b)) not in pairs and (min(a,b),max(a,b)) not in pairs]
            if not opts: ok=False; break
            a,b=rng.choice(opts); L=tuple(sorted((p,a,b))); lines.append(L)
            for x in L: deg[x]+=1
            for x,y in itertools.combinations(L,2): pairs.add((x,y))
        if ok and all(d==3 for d in deg): return lines
    return None
def analyse(lines):
    n=len(lines); S=[set(l) for l in lines]
    meet=[[ (i!=j and bool(S[i]&S[j])) for j in range(n)] for i in range(n)]
    # max clique (size<=7)
    nb=[{j for j in range(n) if meet[i][j]} for i in range(n)]
    best=0
    def bk(R,P):
        nonlocal best
        if len(R)>best: best=len(R)
        if len(R)+len(P)<=best: return
        for v in list(P):
            bk(R|{v},P&nb[v]); P=P-{v}
    bk(set(),set(range(n)))
    tris=[(i,j,k) for i,j,k in itertools.combinations(range(n),3) if meet[i][j] and meet[j][k] and meet[i][k] and not (S[i]&S[j]&S[k])]
    return best,tris
def two_colorable(n,tris):
    inc=[[] for _ in range(n)]
    for t in tris:
        for v in t: inc[v].append(t)
    col=[-1]*n
    order=sorted(range(n),key=lambda v:-len(inc[v]))
    def rec(k):
        if k==n: return True
        v=order[k]
        for c in (0,1):
            col[v]=c
            if all(not(col[a]==col[b]==col[c2]==c) for (a,b,c2) in inc[v] if -1 not in (col[a],col[b],col[c2])):
                if rec(k+1): return True
        col[v]=-1; return False
    return rec(0), col[:]
if __name__=='__main__':
    seed=int(sys.argv[1]); ns=list(map(int,sys.argv[2].split(','))); rng=random.Random(seed); t0=time.time(); stats={}
    while time.time()-t0<cpu-20:
        n=rng.choice(ns); L=random_config(n,rng)
        if L is None: continue
        w,tris=analyse(L); key=(n,w); st=stats.setdefault(str(key),[0,0]); st[0]+=1
        if w<=4:
            ok,_=two_colorable(n,tris)
            if not ok:
                st[1]+=1; print(json.dumps({'COUNTEREXAMPLE_CANDIDATE':L,'n':n,'omega':w,'triangles':len(tris)}),flush=True)
        elif w>=5:
            ok,_=two_colorable(n,tris)
            if not ok: st[1]+=1
    print(json.dumps({'seed':seed,'stats(n,omega)->[count,non2colorable]':stats}))
