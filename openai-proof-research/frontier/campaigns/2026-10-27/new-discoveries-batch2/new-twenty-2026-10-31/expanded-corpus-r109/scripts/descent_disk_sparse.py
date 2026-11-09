# Structured extension for 339411: all I with |I|<=2 and max m in [21, MMAX]; high-precision roots (mpmath), diagnostic.
import sys, json, math, mpmath
MMAX=int(sys.argv[1]); out=sys.argv[2]; mpmath.mp.dps=int(sys.argv[3]) if len(sys.argv)>3 else 60
def d_vals(I,T):
    vals=[1]*(T+1)
    for m2 in I:
        a=vals[m2]; vals=[math.comb(t,m2)*a-vals[t] for t in range(T+1)]
    return vals
def coeffs(vals,m):
    # exact rational monomial coefficients via Newton differences (scaled by m!)
    d=list(vals[:m+1]); c=[]
    for k in range(m+1): c.append(d[0]); d=[d[i+1]-d[i] for i in range(len(d)-1)]
    P=[0]*(m+1); F=math.factorial(m)
    fall=[1]
    for k in range(m+1):
        s=c[k]*(F//math.factorial(k))
        for i,f in enumerate(fall): P[i]+=s*f
        nf=[0]*(len(fall)+1)
        for i,f in enumerate(fall): nf[i+1]+=f; nf[i]-=k*f
        fall=nf
    return P
res={}; viol=[]
for m in range(21,MMAX+1):
    best=(1e9,None)
    for I in [[m]]+[[k,m] for k in range(1,m)]:
        P=coeffs(d_vals(I,m),m)
        hi=[mpmath.mpf(x) for x in P[::-1]]
        # deflate exact root z=m
        q=[hi[0]]
        for a in hi[1:]: q.append(a+m*q[-1])
        assert q[-1]==0; hi=q[:-1]
        rr=mpmath.polyroots(hi,maxsteps=2000,extraprec=2*m*10) if len(hi)>1 else []
        c=mpmath.mpf(m-1)/2; R=mpmath.mpf(m+1)/2
        mm=min([R-abs(z-c) for z in rr],default=R)
        if mm/R<best[0]: best=(float(mm/R),I)
        if mm<0: viol.append({'I':I,'margin':float(mm)})
    res[m]=best; print(m,best,flush=True)
json.dump({'family':'|I|<=2','m_range':[21,MMAX],'min_relative_margin':res,'violations':viol},open(out,'w'),indent=1)
