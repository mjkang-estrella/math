# Randic energy of all free trees on n vertices; report the maximisers and compare with sun / balanced double sun.
import sys,cmath,math,json,time
n=int(sys.argv[1]); METHOD=sys.argv[2] if len(sys.argv)>2 else 'dk'; H=float(sys.argv[3]) if len(sys.argv)>3 else 0.1; TMAX=float(sys.argv[4]) if len(sys.argv)>4 else 30.0
def rooted_level_sequences(n):
    # Beyer-Hedetniemi: all rooted trees as canonical level sequences
    L=list(range(n))
    while True:
        yield L
        p=n-1
        while p>0 and L[p]==1: p-=1
        if p==0: return
        q=p-1
        while L[q]!=L[p]-1: q-=1
        L=L[:p]+[L[i-p+q] for i in range(p,n)]
def adj_from_levels(L):
    n=len(L); par=[-1]*n; stack=[]
    adj=[[] for _ in range(n)]
    for i,l in enumerate(L):
        while len(stack)>l: stack.pop()
        if stack: p=stack[-1]; adj[p].append(i); adj[i].append(p)
        stack.append(i)
    return adj
def canon(adj):
    n=len(adj)
    # centers
    deg=[len(a) for a in adj]; leaves=[v for v in range(n) if deg[v]<=1]; rem=n; d=deg[:]
    layer=leaves
    removed=[False]*n
    while rem>2:
        rem-=len(layer); nxt=[]
        for v in layer:
            removed[v]=True
            for u in adj[v]:
                if not removed[u]:
                    d[u]-=1
                    if d[u]==1: nxt.append(u)
        layer=nxt
    centers=[v for v in range(n) if not removed[v]]
    def enc(v,p):
        return '('+''.join(sorted(enc(u,v) for u in adj[v] if u!=p))+')'
    if len(centers)==1: return enc(centers[0],-1)
    a,b=centers
    return ''.join(sorted([enc(a,b),enc(b,a)]))
def randic_energy(adj):
    n=len(adj); deg=[len(a) for a in adj]
    # matching polynomial with weights 1/(du dv): tree DP rooted at 0
    order=[]; par=[-1]*n; st=[0]; seen=[False]*n; seen[0]=True
    while st:
        v=st.pop(); order.append(v)
        for u in adj[v]:
            if not seen[u]: seen[u]=True; par[u]=v; st.append(u)
    A=[None]*n; B=[None]*n  # A[v]: v unmatched (poly in k), B[v]: v matched to a child
    def add(p,q):
        r=[0.0]*max(len(p),len(q))
        for i,x in enumerate(p): r[i]+=x
        for i,x in enumerate(q): r[i]+=x
        return r
    def mul(p,q):
        r=[0.0]*(len(p)+len(q)-1)
        for i,x in enumerate(p):
            if x:
                for j,y in enumerate(q): r[i+j]+=x*y
        return r
    for v in reversed(order):
        ch=[u for u in adj[v] if u!=par[v]]
        T=[1.0]
        for u in ch: T=mul(T,add(A[u],B[u]))
        A[v]=T
        Bv=[0.0]
        for u in ch:
            prod=[1.0]
            for w in ch:
                if w!=u: prod=mul(prod,add(A[w],B[w]))
            prod=mul(prod,A[u]); w8=1.0/(deg[u]*deg[v])
            Bv=add(Bv,[0.0]+[x*w8 for x in prod])
        B[v]=Bv
    m=add(A[0],B[0])  # m[k] = weighted k-matchings
    K=len(m)-1
    while K>0 and abs(m[K])<1e-300: K-=1
    # char poly in y=x^2 (up to factor x^{n-2K}): sum_k (-1)^k m_k y^{K-k}; roots y>=0
    if K==0: return 0.0
    if METHOD=='coulson':
        # E = (2/pi) int_R e^{-t} ln(sum_k m_k e^{2kt}) dt, trapezoid in t
        h=H; tot=0.0; t=-TMAX
        mm=m[:K+1]
        while t<=TMAX:
            y=math.exp(2*t); acc=0.0; yp=1.0
            for x in mm: acc+=x*yp; yp*=y
            tot+=math.exp(-t)*math.log(acc); t+=h
        return 2/math.pi*tot*h
    c=[((-1)**k)*m[k] for k in range(K+1)]  # c[0] y^K + c[1] y^{K-1} + ...
    roots=[complex(0.4,0.9)**i for i in range(K)]
    for it in range(500):
        delta=0
        new=[]
        for i,z in enumerate(roots):
            pz=0j
            for a in c: pz=pz*z+a
            den=1+0j
            for j,w in enumerate(roots):
                if j!=i: den*=(z-w)
            z2=z-pz/den; delta=max(delta,abs(z2-z)); new.append(z2)
        roots=new
        if delta<1e-14: break
    return 2*sum(math.sqrt(max(0.0,r.real)) for r in roots)
def sun(p):
    adj=[[] for _ in range(2*p+1)]
    for i in range(p):
        a=1+2*i; b=a+1; adj[0]+= [a]; adj[a]+=[0,b]; adj[b]+=[a]
    return adj
def double_sun(p,q):
    s1=sun(p); s2=sun(q); off=len(s1)
    adj=[list(x) for x in s1]+[[y+off for y in x] for x in s2]
    adj[0].append(off); adj[off].append(0)
    return adj
t0=time.time()
seen=set(); res=[]
for L in rooted_level_sequences(n):
    adj=adj_from_levels(L); c=canon(adj)
    if c in seen: continue
    seen.add(c); res.append((randic_energy(adj),c))
res.sort(reverse=True)
if n%2: ref=randic_energy(sun((n-1)//2)); refc=canon(sun((n-1)//2)); name='sun'
else:
    p=(n-2)//2; q=p//2; refadj=double_sun(p-q, q); ref=randic_energy(refadj); refc=canon(refadj); name='balanced double sun'
def describe(c):
    # parse canonical string(s) into adjacency and report degree sequence + branch structure
    return c
print(json.dumps({'top5_canon':[cc for e,cc in res[:5]], 'top5_RE':[e for e,cc in res[:5]]}))
print(json.dumps({'n':n,'free_trees':len(seen),'max_RE':res[0][0],'argmax_is_conjectured':res[0][1]==refc,'conj_graph':name,'conj_RE':ref,'top3':[(round(e,12),cc==refc) for e,cc in res[:3]],'gap':res[0][0]-res[1][0] if len(res)>1 else None,'secs':round(time.time()-t0,1)}))
