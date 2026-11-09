import numpy as np, math, sys, json
def phit(p,q,r):
    """Coefficients of pseudocyclotomic Phi~_{p,q,r} via
    (1-x^{pqr})(1-x^p)(1-x^q)(1-x^r) / ((1-x)(1-x^{pq})(1-x^{pr})(1-x^{qr})) truncated at its degree."""
    D=(p-1)*(q-1)*(r-1); N=D+1
    a=np.zeros(N,dtype=np.int64); a[0]=1
    for e in (p,q,r,p*q*r):
        if e<N: a[e:]=a[e:]-a[:N-e].copy()  # multiply by (1-x^e) (in-place safe via copy)
    for e in (1,p*q,p*r,q*r):
        if e<N:
            if e*e<N:
                for s in range(e):
                    a[s::e]=np.cumsum(a[s::e])   # divide by (1-x^e)
            else:
                for k in range(e,N,e):
                    end=min(k+e,N)
                    a[k:end]+=a[k-e:end-e]
    return a
def check(p,q,r,a):
    w=min(r%(p*q),(-r)%(p*q))
    if (p-1)%w==0: return None  # hypothesis p≢1 (mod w) fails
    viol=[]
    if not w>p: viol.append('w>p')
    if not q>p*p-p: viol.append('q>p^2-p')
    if q%p not in (1,p-1): viol.append('q=±1 mod p')
    if w%p not in (1,p-1): viol.append('w=±1 mod p')
    return w,viol
if __name__=='__main__':
    P=int(sys.argv[1]); Q=int(sys.argv[2]); mode=sys.argv[3]; odd=mode=='odd'
    found=[]
    for p in range(2,P+1):
        if odd and p%2==0: continue
        if mode=='even4' and (p%2==1 or p==2): continue
        for q in range(p+1,Q+1):
            if math.gcd(p,q)!=1: continue
            for w in range(1,p*q//2+1):
                if math.gcd(w,p*q)!=1: continue
                r=w
                while r<=q: r+=p*q
                a=phit(p,q,r)
                assert a[-1]!=0 and a[0]==1
                if np.abs(a).max()!=1: continue
                c=check(p,q,r,a)
                if c is None: continue
                w_,viol=c
                if w_%p==1 and q%(w_*p)==1: viol.append('q≢1 mod wp (pseudo)')
                if viol:
                    found.append((p,q,r,w_,viol)); print('FLAT VIOLATION',p,q,r,'w',w_,viol,flush=True)
    print('done',len(found))
