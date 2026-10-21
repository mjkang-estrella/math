"""Finite sanity checks of the paired local calculation; no universal gate."""
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path

def val(x,p):
    x=F(x)
    if not x:return 10**6
    a,b=x.numerator,x.denominator; v=0
    while a%p==0:a//=p;v+=1
    while b%p==0:b//=p;v-=1
    return v

def multiplication(a,p):
    # Basis (1,...,1), p e_2,...,p e_n for Z_p+p Z_p^n.
    n=len(a);M=[[F(0) for _ in range(n)] for _ in range(n)]
    M[0][0]=a[0]
    for i in range(1,n):M[i][0]=(a[i]-a[0])/p;M[i][i]=a[i]
    return M

def smith_valuations(M,p):
    M=[r[:] for r in M];n=len(M);out=[]
    for k in range(n):
        v,i,j=min((val(M[i][j],p),i,j) for i in range(k,n) for j in range(k,n))
        if v==10**6:return out+[v]*(n-k)
        M[k],M[i]=M[i],M[k]
        for r in M:r[k],r[j]=r[j],r[k]
        for i in range(k+1,n):
            q=M[i][k]/M[k][k]
            for j in range(k,n):M[i][j]-=q*M[k][j]
        for j in range(k+1,n):
            q=M[k][j]/M[k][k]
            for i in range(k,n):M[i][j]-=q*M[i][k]
        out.append(v)
    return out

def gamma(a,p):
    vs=smith_valuations(multiplication(a,p),p)
    return F(1,p**sum(max(0,-v) for v in vs))

def brute(a,p):
    M=multiplication(a,p);k=max(0,max(-val(x,p) for row in M for x in row))
    modulus=p**k
    # Only bounded cases supplied below: at most 4^6 residue vectors.
    A=[[int(x*modulus)%modulus for x in row] for row in M]
    count=0
    for x in product(range(modulus),repeat=len(a)):
        count+=all(sum(c*z for c,z in zip(row,x))%modulus==0 for row in A)
    return F(count,modulus**len(a)),modulus**len(a)

def main():
    rows=[]
    cases=[(2,[F(1,2),1,1,1,1,1]),(2,[0,1,0,1,0,1]),
           (2,[F(1,2)]*6),(3,[F(1,3),1,2]),(3,[1,2,4]),(2,[1,1,1,1,1,3])]
    for p,a in cases:
        a=list(map(F,a));g=gamma(a,p);b,N=brute(a,p);assert g==b
        for s in range(7):assert gamma([x+s for x in a],p)==g
        inverse=None
        if all(a):
            norm=F(1)
            for x in a:norm*=x
            norm_abs=F(p)**(-val(norm,p))
            inverse=gamma([1/x for x in a],p)/norm_abs
            assert g==inverse
        rows.append(dict(p=p,a=list(map(str,a)),gamma=str(g),enumerated=N,inverse_identity=None if inverse is None else str(inverse)))
    n=6;trace=[]
    for p in [2,3]:
        counts=[0]*p;xs=list(product(range(p),repeat=n))
        for x in xs:
            for y in xs:counts[sum(a*b for a,b in zip(x,y))%p]+=1
        expected=[p**(2*n-1)+(p-1)*p**(n-1)]+[p**(2*n-1)-p**(n-1)]*(p-1)
        assert counts==expected
        trace.append(dict(p=p,n=n,counts=counts,pairs=p**(2*n)))
    # Candidate bookkeeping parameters only: they do not verify the analytic proof.
    d=e=F(1,10000);e1=e/100;e2=e1/100;w=e2/1000;tau=w/100;eps=e2/4
    margins={'small_G':F(1,6)-F(3,2)*d-F(289,2)*e,
             'large_J':e2/2-6*w,'small_primes_congruences':e1/2-6*w,
             'large_prime_congruence':min(e1,F(1,120))-6*w,
             'real_tail':(1000-6)*w-1000*tau}
    for k in range(6):margins[f'large_field_k{k}']=(1-F(k,6))*(d/30-w)-k*w
    margins['large_field_volume']=d/2-6*w
    assert all(m>eps for m in margins.values())
    assert e/6-e2>2*e1 and 2*e1<F(1,120) and w+e2<F(1,60) and eps>6*tau
    return {'status':'finite identities and rational margins reproduced; not a mathematical gate',
            'index_cases':rows,'trace_cases':trace,'margins':{k:str(v) for k,v in margins.items()},
            'parameters':{k:str(v) for k,v in dict(d=d,e=e,e1=e1,e2=e2,w=w,tau=tau,eps=eps).items()}}

if __name__=='__main__':
    print(json.dumps(main(),indent=2))
