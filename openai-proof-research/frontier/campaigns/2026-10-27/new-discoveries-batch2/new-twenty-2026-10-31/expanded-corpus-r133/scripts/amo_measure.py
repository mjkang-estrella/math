# |Sigma_{p/q}| for critical almost Mathieu (lambda=1): Sigma = {E : |D(E)| <= 4},
# D(E) = tr M(E, theta=1/(4q)) (Chambers: tr M(E,theta) = D(E) - 2cos(2 pi q theta)).
# Diagnostic floating-point computation (double precision); not a certificate.
import math, sys
UNRESOLVED=0
def pot(p,q,th): return [2*math.cos(2*math.pi*(p*n/q+th)) for n in range(q)]
def D(E,v):
    # transfer matrix product for psi_{n+1} = (E - v_n) psi_n - psi_{n-1}
    a,b,c,d=1.0,0.0,0.0,1.0   # M = [[a,b],[c,d]]
    for vn in v:
        t=E-vn
        a,b,c,d = t*a-c, t*b-d, a, b
        s=max(abs(a),abs(b),abs(c),abs(d))
        # no rescaling: trace needed exactly; values bounded on region of interest
    return a+d
def sturm_count(E,v):  # eigenvalues < E of Dirichlet matrix on sites 1..q-1 (diag v[1..q-1], offdiag 1)
    cnt=0; x=1.0
    for i in range(1,len(v)):
        x=(v[i]-E)-(1.0/x if i>1 else 0.0)
        if x==0: x=1e-300
        if x<0: cnt+=1
    return cnt
def dirichlet_eigs(v):
    q=len(v); eig=[]
    for k in range(q-1):
        lo,hi=-4.5,4.5
        for _ in range(60):
            mid=(lo+hi)/2
            if sturm_count(mid,v)<=k: lo=mid
            else: hi=mid
        eig.append((lo+hi)/2)
    return eig
def bisect(f,lo,hi,it=80):
    flo=f(lo)
    for _ in range(it):
        mid=(lo+hi)/2; fm=f(mid)
        if (fm>0)==(flo>0): lo,flo=mid,fm
        else: hi=mid
    return (lo+hi)/2
def measure(p,q):
    v=pot(p,q,1/(4*q)); f=lambda E: D(E,v)
    mu=[-4.5]+dirichlet_eigs(v)+[4.5]
    pts=[]
    for i in range(q):
        pts += [mu[i], (mu[i]+mu[i+1])/2]
    pts.append(mu[q])
    vals=[f(x) for x in pts]
    roots=[]
    for i in range(len(pts)-1):
        if (vals[i]>0)!=(vals[i+1]>0): roots.append(bisect(f,pts[i],pts[i+1]))
    global UNRESOLVED
    UNRESOLVED=q-len(roots)
    # edges: left of first root, between roots, right of last root
    total=0.0; edges=[]
    g=lambda E: abs(f(E))-4
    # leftmost: D(-4.5) large in abs; edge between -4.5 and roots[0]
    left=bisect(g,-4.5,roots[0]); edges.append(left)
    for i in range(len(roots)-1):
        a,b=roots[i],roots[i+1]
        # unimodal |D| on (a,b): golden-section max
        lo,hi=a,b; gr=(math.sqrt(5)-1)/2
        x1=hi-gr*(hi-lo); x2=lo+gr*(hi-lo); f1=abs(f(x1)); f2=abs(f(x2))
        for _ in range(90):
            if f1<f2: lo=x1; x1=x2; f1=f2; x2=lo+gr*(hi-lo); f2=abs(f(x2))
            else: hi=x2; x2=x1; f2=f1; x1=hi-gr*(hi-lo); f1=abs(f(x1))
        c=(lo+hi)/2
        if abs(f(c))<=4:  # closed gap
            edges.append(None); continue
        e1=bisect(g,a,c); e2=bisect(g,c,b); edges.append((e1,e2))
    right=bisect(g,roots[-1],4.5)
    # measure = (right-left) - sum of gap lengths
    gaps=sum(e[1]-e[0] for e in edges[1:] if e is not None)
    return (right-left)-gaps
if __name__=='__main__':
    G=32*0.915965594177219015054603514932384110774/math.pi
    mode=sys.argv[1]
    if mode=='check':
        for q in (3,5,7,9,11,21,51,95):
            ms=[(p, q*measure(p,q)) for p in range(1,q) if math.gcd(p,q)==1]
            m1=dict(ms)[1]; worst_mid=min((v-m1,p) for p,v in ms if p not in (1,q-1)) if q>3 else None
            print(q, 'q|S_1/q|',m1, 'max q|S|',max(v for _,v in ms), 'G-max', G-max(v for _,v in ms), 'min(q|S_p|-q|S_1|) p!=1,q-1', worst_mid, flush=True)
    elif mode=='scan':
        qlo,qhi=int(sys.argv[2]),int(sys.argv[3])
        for q in range(qlo,qhi+1,2):
            ms=[(p, q*measure(p,q)) for p in range(1,(q+1)//2) if math.gcd(p,q)==1]  # symmetry p <-> q-p
            m1=dict(ms)[1]; mx=max(ms,key=lambda t:t[1])
            mid=min(((v-m1),p) for p,v in ms if p!=1)
            print(q,'q|S1|',repr(m1),'max',mx,'G-max',G-mx[1],'mid_min',mid, flush=True)
    elif mode=='p12':
        qlo,qhi=int(sys.argv[2]),int(sys.argv[3])
        for q in range(qlo,qhi+1,2):
            a=q*measure(1,q); b=q*measure(2,q)
            print(q, repr(a), repr(b), 'diff', b-a, 'G-a', G-a, 'G-b', G-b, flush=True)
