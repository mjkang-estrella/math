# Cross-validation for 342364: exact integers (no modulus).
# (a) c_m(n) computed from the product definition 1/(1-x)^m * prod_i (1-x^{2^i})^{-m};
# (b) series of C^m(x) * d_j(y), y=x/(1-x), compared with c_m(2^j(4n)) - c_m(2^j n) for n<=N.
import sys, json
sys.path.insert(0, __import__('os').path.dirname(__file__))
from tcheb import T, add
m=int(sys.argv[1]); N=int(sys.argv[2]); J=int(sys.argv[3])
L=4*N*2**J+1
a=[1]+[0]*(L-1)
def inv1(a,p):  # multiply by 1/(1-x^p)
    for n in range(p,L): a[n]+=a[n-p]
for _ in range(m): inv1(a,1)
p=1
while p<L:
    for _ in range(m): inv1(a,p)
    p*=2
c=a
# C^m truncated to N terms is c itself; y^E series
def yser(E,M):
    # x^E/(1-x)^E coefficients up to M
    from math import comb
    return [comb(n-1,E-1) if n>=E and E>0 else (1 if (E==0 and n==0) else 0) for n in range(M)]
A=[[1]]
for j in range(J+2): A.append(T(A[-1],m))
ok=True; rep=[]
for j in range(J):
    d=add(A[j+2],A[j],-1); M=N+1
    s=[0]*M
    for E,coef in enumerate(d):
        if coef:
            ys=yser(E,M)
            for n in range(M): s[n]+=coef*ys[n]
    prod=[sum(c[i]*s[n-i] for i in range(n+1)) for n in range(M)]
    target=[c[4*n*2**j]-c[n*2**j] for n in range(M)]
    good=prod==target; ok&=good; rep.append(dict(j=j,match=good))
print(json.dumps(dict(m=m,N=N,J=J,all_match=ok,rows=rep,c_first=[c[i] for i in range(6)],diff_n1=c[4]-c[1])))
