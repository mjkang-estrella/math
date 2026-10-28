"""Exact rational coefficient tests; identities are proved generally in PROOF.md."""
from fractions import Fraction as Q
from math import prod
from pathlib import Path
import json

def qi(n,q):return sum(q**j for j in range(n))
def qb(n,k,q):
 if k<0 or k>n:return Q(0)
 return prod((qi(n+1-j,q)/qi(j,q) for j in range(1,k+1)),start=Q(1))
def F(n,m,q):return [q**(m*k*(k+1)//2)*prod(qb(n,k+j,q) for j in range(m)) for k in range(n-m+2)]
def mac(k,l,m,q):return prod((1-q**(l+i+j-1))/(1-q**(i+j-1)) for i in range(1,k+1) for j in range(1,m+1))

def main():
 cases=0;bridges=0
 for q in [Q(11,10),Q(3,2),Q(2),Q(3)]:
  for m in range(2,8):
   for n in range(m,m+12):
    a,b=F(n,1,q),F(n-1,m-1,q)
    G=[x*y for x,y in zip(a,b)]
    L=[qi(k+1,q)*G[k+1] for k in range(len(G)-1)]
    R=[qi(n,q)*q**(m*(k+1))*v for k,v in enumerate(F(n-1,m,q))]
    assert L==R,(q,n,m);cases+=1
   for N in range(1,10):
    n=N+m-1
    for k in range(N+1):
     a=prod(qb(n,k+j,q) for j in range(m))/prod(qb(n,j,q) for j in range(1,m))
     assert a==mac(k,N-k,m,q),(q,N,m,k);bridges+=1
 out=dict(status='PASS',coefficient_identity_cases=cases,macmahon_normalization_cases=bridges,arithmetic='fractions.Fraction, exact',note='Finite corroboration of general proofs; no numerical root evidence used in the theorem')
 print(out);Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2))
if __name__=='__main__':main()
