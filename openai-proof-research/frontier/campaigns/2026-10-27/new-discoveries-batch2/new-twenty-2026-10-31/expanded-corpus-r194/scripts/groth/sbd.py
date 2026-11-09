# Hafner arXiv:2602.02448v1 Conjecture 5.2 check: for almost vexillary w, does some A subset of D(w) satisfy
# supp(G_w) = { wt(D) : D in SBD(D(w), {}, A) } ?
import sys, itertools, json, pathlib
n=int(sys.argv[1]); mode=sys.argv[2]; out=pathlib.Path(sys.argv[3])
lo=int(sys.argv[4]) if len(sys.argv)>4 else 0; hi=int(sys.argv[5]) if len(sys.argv)>5 else 10**9
def dd(f,i):  # isobaric pi_i f = d_i((1-x_{i+1}) f), variables 0-based i,i+1
    g={}
    def add(e,c):
        g[e]=g.get(e,0)+c
        if g[e]==0: del g[e]
    h={}
    for e,c in f.items():
        h[e]=h.get(e,0)+c
        e2=list(e); e2[i+1]+=1; e2=tuple(e2); h[e2]=h.get(e2,0)-c
    for e,c in h.items():
        if c==0: continue
        a,b=e[i],e[i+1]
        if a==b: continue
        if a>b:
            for k in range(a-b):
                e2=list(e); e2[i]=a-1-k; e2[i+1]=b+k; add(tuple(e2),c)
        else:
            for k in range(b-a):
                e2=list(e); e2[i]=b-1-k; e2[i+1]=a+k; add(tuple(e2),-c)
    return g
def groth_all(n):
    w0=tuple(range(n,0,-1)); G={w0:{tuple(n-1-i for i in range(n)):1}}
    layer=[w0]
    while layer:
        nxt=[]
        for w in layer:
            for i in range(n-1):
                if w[i]>w[i+1]:
                    v=list(w); v[i],v[i+1]=v[i+1],v[i]; v=tuple(v)
                    if v not in G: G[v]=dd(G[w],i); nxt.append(v)
        layer=nxt
    return G
def contains(w,p):
    k=len(p)
    for idx in itertools.combinations(range(len(w)),k):
        vals=[w[t] for t in idx]
        if all((vals[a]<vals[b])==(p[a]<p[b]) for a in range(k) for b in range(a+1,k)): return True
    return False
def rothe(w):
    n=len(w); winv={w[i]:i+1 for i in range(n)}
    return frozenset((i,j) for i in range(1,n+1) for j in range(1,n+1) if i<winv[j] and j<w[i-1])
def sbd_weights(D,A,n,cap=200000):
    start=(D,frozenset(),frozenset(A)); seen={start}; st=[start]; W=set()
    while st:
        Dc,Fc,Ac=st.pop()
        W.add(tuple(sum(1 for (i,j) in Dc if i==r) for r in range(1,n+1)))
        for (i,j) in Dc:
            if (i,j) in Fc or i==1 or (i-1,j) in Dc: continue
            nA = (Ac-{(i,j)})|{(i-1,j)} if (i,j) in Ac else Ac
            s1=((Dc-{(i,j)})|{(i-1,j)},Fc,nA)
            if s1 not in seen: seen.add(s1); st.append(s1)
            if (i,j) in Ac:
                s2=(Dc|{(i-1,j)},Fc|{(i,j)},(Ac-{(i,j)})|{(i-1,j)})
                if s2 not in seen: seen.add(s2); st.append(s2)
        if len(seen)>cap: return None
    return W
G=groth_all(n)
vex=lambda w: not contains(w,(2,1,4,3))
almost=lambda w: not any(contains(w,p) for p in [(1,3,2,5,4),(3,1,5,2,6,4),(3,1,6,2,5,4)])
perms=sorted(G)
res=[]; cnt=0
for w in perms:
    if mode=='vex' and not vex(w): continue
    if mode=='almost' and not (almost(w) and not vex(w)): continue
    cnt+=1
    if not (lo<=cnt<=hi): continue
    D=rothe(w); supp=set(G[w]); Dl=sorted(D)
    found=None; tried=0; one_per_col_only=True
    # first: subsets with at most one square per column, then all subsets
    cols={}
    for s in Dl: cols.setdefault(s[1],[]).append(s)
    def gen_onepercol():
        for choice in itertools.product(*[[None]+c for c in cols.values()]):
            yield frozenset(x for x in choice if x is not None)
    for A in gen_onepercol():
        tried+=1; W=sbd_weights(D,A,n)
        if W is not None and W==supp: found=sorted(A); break
    if found is None:
        one_per_col_only=False
        for r in range(len(Dl)+1):
            for A in itertools.combinations(Dl,r):
                A=frozenset(A)
                if all(sum(1 for x in A if x[1]==c)<=1 for c in cols): continue
                tried+=1; W=sbd_weights(D,A,n)
                if W is not None and W==supp: found=sorted(A); break
            if found is not None: break
    res.append(dict(w=''.join(map(str,w)),len=len(D),supp=len(supp),found=found,tried=tried))
    if found is None: print('NO A FOUND',w,len(D),flush=True)
print(mode,'n',n,'checked',len(res),'failures',sum(1 for r in res if r['found'] is None))
out.write_text(json.dumps(res,indent=0))
