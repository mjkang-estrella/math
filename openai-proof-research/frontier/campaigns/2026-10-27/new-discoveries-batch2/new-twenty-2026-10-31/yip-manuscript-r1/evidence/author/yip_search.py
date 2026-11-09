# Exact search: for odd prime powers q=p^m, d>1 with q≡1 mod 2d, r = largest r|m with d | (q-1)/(p^r-1),
# test whether subfield F_{p^r} is a maximal clique in GP(q,d)=Cay(F_q^+, (F_q^*)^d).
# Field arithmetic: F_p[X]/(f) with f found irreducible by exhaustive check (Rabin test).
import sys, itertools, json, resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3)); resource.setrlimit(resource.RLIMIT_CPU,(int(sys.argv[2]) if len(sys.argv)>2 else 600,)*2)
def polymulmod(a,b,f,p):
    m=len(f)-1; res=[0]*(2*m-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b):
                if y: res[i+j]=(res[i+j]+x*y)%p
    for k in range(len(res)-1,m-1,-1):
        c=res[k]
        if c:
            for t in range(m+1): res[k-m+t]=(res[k-m+t]-c*f[t])%p
    return res[:m]
def polypow(a,e,f,p):
    m=len(f)-1; r=[1]+[0]*(m-1); b=a[:]
    while e:
        if e&1: r=polymulmod(r,b,f,p)
        b=polymulmod(b,b,f,p); e>>=1
    return r
def _trim(a):
    while a and a[-1]==0: a=a[:-1]
    return a
def _pgcd(a,b,p):
    a=_trim(a[:]); b=_trim(b[:])
    while b:
        inv=pow(b[-1],p-2,p)
        while len(a)>=len(b):
            c=a[-1]*inv%p; sh=len(a)-len(b)
            for i,y in enumerate(b): a[sh+i]=(a[sh+i]-c*y)%p
            a=_trim(a)
            if not a: break
        a,b=b,a
    return a
def _prime_factors(n):
    r=[];k=2
    while k*k<=n:
        if n%k==0:
            r.append(k)
            while n%k==0: n//=k
        k+=1
    if n>1: r.append(n)
    return r
def is_irreducible(f,p):
    # Rabin's test: X^(p^m) = X mod f, and gcd(X^(p^(m/l)) - X, f) = 1 for each prime l | m.
    m=len(f)-1
    if m==1: return True
    X=[0,1]+[0]*(m-2)
    if polypow(X,p**m,f,p)!=X: return False
    for l in _prime_factors(m):
        h=polypow(X,p**(m//l),f,p); h=[(h[i]-X[i])%p for i in range(m)]
        g=_pgcd(f[:],h,p)
        if len(g)!=1: return False
    return True
def find_irred(p,m):
    for tail in itertools.product(range(p),repeat=m):
        f=list(tail)+[1]
        if f[0]==0: continue
        if is_irreducible(f,p): return f
def divisors(n): return [k for k in range(1,n+1) if n%k==0]
def analyse(p,m,limit_witnesses=5):
    q=p**m; f=find_irred(p,m); out=[]
    for d in range(2,q):
        if (q-1)%(2*d): continue
        rs=[r for r in divisors(m) if ((q-1)//(p**r-1))%d==0]
        if not rs: continue
        r=max(rs)
        if r==m: continue  # (q-1)/(q-1)=1 not divisible by d>1, cannot happen
        e=(q-1)//d
        # subfield F_{p^r} = {y : y^(p^r)=y}
        elems=[list(t) for t in itertools.product(range(p),repeat=m)]
        def isdpow(v): return any(v) and polypow(v,e,f,p)==[1]+[0]*(m-1)
        sub=[v for v in elems if polypow(v,p**r,f,p)==v]
        assert len(sub)==p**r
        # check clique (sanity)
        assert all(isdpow([(a-b)%p for a,b in zip(u,w)]) for u in sub for w in sub if u!=w)
        subset=set(map(tuple,sub)); wit=[]
        for v in elems:
            if tuple(v) in subset: continue
            if all(isdpow([(a-b)%p for a,b in zip(v,s)]) for s in sub):
                wit.append(v)
                if len(wit)>=limit_witnesses: break
        out.append({'q':q,'p':p,'m':m,'d':d,'r':r,'n':m//r,'modulus_coeffs_low_to_high':f,'thm_hyp_p^r>(n-1)^2':p**r>(m//r-1)**2,'extension_witnesses':wit,'maximal':not wit})
    return out
if __name__=='__main__':
    p,m=map(int,sys.argv[1].split(','))
    for row in analyse(p,m): print(json.dumps(row),flush=True)
