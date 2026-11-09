from math import comb,gcd
from fractions import Fraction
from pathlib import Path
import json,datetime
C=lambda a,b: comb(a,b) if 0<=b<=a else 0
def P(r,k,i): return C(k,i)*C(k+r+i-1,i)
def A(r,i,j,l):
    return C(l,i)*C(l,j)*C(r+i+j-1,i+j-l) if l>=0 else 0
def S(r,n,l): return (n+r-1)*C(n,l+1)*C(n+r+l-1,l)
counts={}
c=0
for r in range(1,25):
 for i in range(10):
  for j in range(10):
   for k in range(25):
    assert P(r,k,i)*P(r,k,j)==sum(A(r,i,j,l)*P(r,k,l) for l in range(max(i,j),i+j+1))
    c+=1
counts['linearization_r1_24_i_j0_9_k0_24']=c
c=0
for r in range(1,25):
 for i in range(14):
  for j in range(14):
   for l in range(i+j+3):
    assert (j+1)**2*A(r,i,j+1,l)==l*l*A(r,i,j,l-1)+(l*(l+r)-j*(j+r))*A(r,i,j,l)
    c+=1
counts['coefficient_recurrence_r1_24_i_j0_13_all_boundaries']=c
c=0
for r in range(1,49):
 for n in range(1,65):
  for l in range(0,n+3):
   assert sum((2*k+r)*P(r,k,l) for k in range(n))==S(r,n,l)
   c+=1
counts['weighted_sum_r1_48_n1_64_l0_nplus2']=c
def vp(a,p):
 t=0
 while a%p==0: a//=p;t+=1
 return t
c=0;pair=0
for p in [2,3,5,7]:
 for e in range(1,5):
  q=p**e
  for R in [1,2,3]:
   r=q*R
   for u in [1,2,3]:
    for delta in [0,1]:
     n=u*q+delta
     # Bounded indices include p-adic trouble near q and n, without giant sweeps.
     for m in sorted(set([1,2,p,q-1,q,q+1,n//2,n-1,n])):
      if not 1<=m<=n:continue
      assert S(r,n,m-1)%q==0
      if delta==0:
       t=vp(m,p);s=min(e,t)
       assert vp(C(n,m),p)>=max(0,e-t)
       assert vp(C(n+r+m-2,m-1),p)>=s
      c+=1
     pair+=1
counts['prime_power_selected_cases']=c;counts['prime_power_n_r_pairs']=pair
c=0
for r in range(1,25):
 for n in range(1,11):
  inv=[[Fraction((-1)**(i+j)*sum((2*k+r)*P(r,k,i)*P(r,k,j) for k in range(n)),r) for j in range(n)] for i in range(n)]
  for i in range(n):
   for j in range(n):
    assert sum(Fraction(1,C(i+k+r,r))*inv[k][j] for k in range(n))==int(i==j)
  assert all(x.denominator==1 for row in inv for x in row)==(n*(n-1)%r==0)
  c+=1
counts['exact_rational_matrix_products_r1_24_n1_10']=c
result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','counts':counts,'scope':'Finite exact controls only; universal proof is PROOF.md; no floating point; no proof by numerical evidence'}
Path(__file__).with_name('check-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
