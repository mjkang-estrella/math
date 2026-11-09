# Diagnostic |Sigma_{p/q}| (critical AMO) via eigenvalues of cyclic Jacobi matrices:
#  D(E)=4  <-> periodic eigenvalues (corner +1) of H_theta, theta=0      (tr M = D - 2 = 2)
#  D(E)=-4 <-> antiperiodic eigenvalues (corner -1) of H_theta, theta=1/(2q) (tr M = D + 2 = -2)
# Eigenvalue counts by Sylvester inertia of B=A-E (cyclic elimination with spike column), Decimal arithmetic.
import math, sys
from decimal import Decimal, getcontext
G=32*0.915965594177219015054603514932384110774/math.pi
def count_below(E,v,corner):
    q=len(v); one=Decimal(1); neg=0
    d=v[0]-E; s=Decimal(corner)
    if d<0: neg+=1
    acc=s*s/d
    for i in range(1,q-1):
        dn=(v[i]-E)-one/d
        sn=(one if i==q-2 else Decimal(0)) - s/d
        if dn==0: dn=Decimal('1e-200')
        d,s=dn,sn
        if d<0: neg+=1
        acc+=s*s/d
    last=(v[q-1]-E)-acc
    if last<0: neg+=1
    return neg
def eigs(v,corner,iters):
    q=len(v); out=[]
    for k in range(q):
        lo,hi=Decimal(-4.6),Decimal(4.6)
        for _ in range(iters):
            mid=(lo+hi)/2
            if count_below(mid,v,corner)<=k: lo=mid
            else: hi=mid
        out.append((lo+hi)/2)
    return out
def measure(p,q,iters=70):
    getcontext().prec=max(40,int(0.6*q)+30)
    v0=[Decimal(2*math.cos(2*math.pi*(p*n/q))) for n in range(q)]
    v1=[Decimal(2*math.cos(2*math.pi*(p*n/q+1/(2*q)))) for n in range(q)]
    e=sorted(eigs(v0,1,iters)+eigs(v1,-1,iters))
    return float(sum(e[2*k+1]-e[2*k] for k in range(q)))
if __name__=='__main__':
    mode=sys.argv[1]
    if mode=='pairs':
        for tok in sys.argv[2:]:
            p,q=map(int,tok.split('/')); m=measure(p,q)
            print(f'{p}/{q}','q|S|',repr(q*m),'G-q|S|',G-q*m,flush=True)
    elif mode=='allp':
        for q in map(int,sys.argv[2:]):
            res=[(p,q*measure(p,q)) for p in range(1,(q+1)//2) if math.gcd(p,q)==1]
            m1=res[0][1]; mx=max(res,key=lambda t:t[1])
            print(q,'q|S1|',repr(m1),'max',mx,'G-max',G-mx[1],'min_mid',min(((r[1]-m1),r[0]) for r in res[1:]),flush=True)
