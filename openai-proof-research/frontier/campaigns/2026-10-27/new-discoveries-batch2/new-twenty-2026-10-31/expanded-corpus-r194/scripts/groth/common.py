import itertools
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
vex=lambda w: not contains(w,(2,1,4,3))
almost=lambda w: not any(contains(w,p) for p in [(1,3,2,5,4),(3,1,5,2,6,4),(3,1,6,2,5,4)])
