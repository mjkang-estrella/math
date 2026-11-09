# Diagnostic (not validated) |Sigma_{p/q}| for critical AMO via band edges:
#  D(E)=4 roots = periodic eigenvalues of H_theta at theta=0 (tr M = D-2),
#  D(E)=-4 roots = antiperiodic eigenvalues at theta=1/(2q) (tr M = D+2).
# Each root bracketed between consecutive Dirichlet eigenvalues of the same H_theta (Sturm, double).
# D evaluated in Decimal with precision ~0.7q+40 digits; potentials rounded to double (eigenvalue shift <= 1e-15).
import math, sys
from decimal import Decimal, getcontext
G=32*0.915965594177219015054603514932384110774/math.pi
def pot(p,q,th): return [2*math.cos(2*math.pi*(p*n/q+th)) for n in range(q)]
def trM(E,vd):
    a,b,c,d=Decimal(1),Decimal(0),Decimal(0),Decimal(1)
    for vn in vd:
        t=E-vn
        a,b,c,d = t*a-c, t*b-d, a, b
    return a+d
def sturm_count(E,v):
    cnt=0; x=None
    for i in range(1,len(v)):
        x=(v[i]-E) if x is None else (v[i]-E)-1.0/x
        if x==0: x=1e-300
        if x<0: cnt+=1
    return cnt
def dirichlet(v):
    q=len(v); out=[]
    for k in range(q-1):
        lo,hi=-4.6,4.6
        for _ in range(64):
            mid=(lo+hi)/2
            if sturm_count(mid,v)<=k: lo=mid
            else: hi=mid
        out.append((lo+hi)/2)
    return out
def root(f,a,b,tol):
    fa,fb=f(a),f(b); side=0
    if fa==0: return a
    if fb==0: return b
    if (fa>0)==(fb>0): return None
    for _ in range(200):
        c=(a*fb-b*fa)/(fb-fa); fc=f(c)
        if fc==0 or abs(b-a)<tol: return c
        if (fc>0)==(fb>0):
            b,fb=c,fc
            if side==-1: fa/=2
            side=-1
        else:
            a,fa=c,fc
            if side==1: fb/=2
            side=1
    return (a+b)/2
def edges(p,q,th,target,tol):
    v=pot(p,q,th); v=v[1:]+v[:1]   # cyclic shift (trace invariant) to avoid reflection-symmetric Dirichlet cut
    vd=[Decimal(x) for x in v]
    f=lambda E: trM(E,vd)-target
    mu=[Decimal(-4.6)]+[Decimal(x) for x in dirichlet(v)]+[Decimal(4.6)]
    out=[]; miss=0
    for i in range(q):
        r=root(f,mu[i],mu[i+1],tol)
        if r is None:
            fa,fb=abs(f(mu[i])),abs(f(mu[i+1]))
            r=mu[i] if fa<fb else mu[i+1]
            if min(fa,fb)>Decimal('1e-10'): miss+=1
        out.append(r)
    return out,miss
def measure(p,q):
    getcontext().prec=max(50,int(0.7*q)+40)
    tol=Decimal(10)**-25
    e4,m1=edges(p,q,0.0,Decimal(2),tol)            # tr M(E,0) = D-2 = 2
    em4,m2=edges(p,q,1/(2*q),Decimal(-2),tol)      # tr M(E,1/2q) = D+2 = -2
    allE=sorted(e4+em4)
    meas=sum(allE[2*k+1]-allE[2*k] for k in range(q))
    return float(meas), m1+m2
if __name__=='__main__':
    mode=sys.argv[1]
    if mode=='pairs':
        for tok in sys.argv[2:]:
            p,q=map(int,tok.split('/'))
            m,miss=measure(p,q)
            print(f'{p}/{q}', 'q|S|',repr(q*m),'G-q|S|',G-q*m,'missed brackets',miss, flush=True)
    elif mode=='allp':
        q=int(sys.argv[2]); res=[]
        for p in range(1,(q+1)//2):
            if math.gcd(p,q)!=1: continue
            m,miss=measure(p,q); res.append((p,q*m,miss))
        m1=res[0][1]
        print(q,'q|S1|',m1,'max',max(res,key=lambda t:t[1]),'G-max',G-max(r[1] for r in res),'min mid',min(((r[1]-m1),r[0]) for r in res[1:]),'miss',sum(r[2] for r in res),flush=True)
