# Exact check of the literal 356309 identity and of the intermediate forms used in the Lagrange-inversion proof.
from fractions import Fraction as F
from math import comb, factorial
def poch(a,i):
    r=F(1)
    for t in range(i): r*=a+t
    return r
def gbinom(a,j):  # generalized binomial C(a,j) for rational a
    r=F(1)
    for t in range(j): r*=(a-t)
    return r/factorial(j)
def lhs(g,l,j):
    c=2-2*g-(l+j); s=F(0)
    for i in range(j+1):
        assert poch(F(c),i)!=0
        s+=poch(F(-j),i)*poch(F(-2*j),i)/(poch(F(c),i)*factorial(i))*(-1)**i
    return factorial(j)*2**(l+2*g-1)*comb(2*g-2+l+j,j)*s
def rhs(g,l,j):
    N=l+2*g; tot=0
    for k in range(1,N+1):
        p=1
        for m in range(j): p*=2*(2*m+k)
        tot+=comb(N-1,k-1)*p
    return tot
def mid1(N,j): return 2**(N-1)*factorial(j)*sum(comb(2*j,i)*comb(N-2+j-i,j-i) for i in range(j+1))
def mid2(N,j): return 4**j*factorial(j)*2**j*sum(comb(N-1,k-1)*gbinom(F(k,2)+j-1,j) for k in range(1,N+1))
bad=0;n=0
for g in range(1,13):
  for l in range(0,25):
    for j in range(1,25):
      N=l+2*g; a=lhs(g,l,j); b=rhs(g,l,j); n+=1
      if not (a==b==mid1(N,j)==mid2(N,j)/2**j*1 or (a==b and a==mid1(N,j))): bad+=1
print('cases',n,'mismatches',bad)
