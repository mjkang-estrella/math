# Independent exact route diagnostics, reusing only the branching implementation.
import runpy,sys,pathlib,json
from fractions import Fraction as F
from itertools import permutations,product
from math import comb,prod
L=pathlib.Path(__file__).resolve().parent
sys.argv=['scan.py','--exact']; S=runpy.run_path(str(L/'scan.py'))
# S contains the q=t=1/2 branch model; compare with Schur determinant.
P=S['poly']; parts=S['parts']
def value(p,z):return sum(c*prod(x**k for x,k in zip(z,e)) for e,c in p.items())
def det(A):
 n=len(A);v=0
 for p in permutations(range(n)):
  inv=sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
  v+=(-1)**inv*prod(A[i][p[i]] for i in range(n))
 return v
schur=0
for n in range(2,5):
 z=[F(j+1) for j in range(n)]
 for d in range(1,7):
  for l in parts(d,n):
   assert value(P(l,n),z)==det([[z[i]**(l[j]+n-j-1) for j in range(n)] for i in range(n)])/det([[z[i]**(n-j-1) for j in range(n)] for i in range(n)])
   schur+=1
# helper exact polynomial operations

def add(a,b):return [(a[k] if k<len(a) else 0)+(b[k] if k<len(b) else 0) for k in range(max(len(a),len(b)))]
def mul(a,b):
 c=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
def der(a):return [k*a[k] for k in range(1,len(a))]
def scale(a,c):return [c*x for x in a]
def numerator(a,b,c):return add(scale(mul(mul(der(b),a),c),2),scale(mul(b,add(mul(der(a),c),mul(a,der(c)))),-1))
def shift(a):return [sum(a[k]*comb(k,j) for k in range(j,len(a))) for j in range(len(a))]
def specialize(p,n,t,d):
 C=[]
 for i in range(n+1):
  a=[F(0)]*(d+1)
  for e,c in p.items():a[sum(e[:i])]+=c*t**sum(j*v for j,v in enumerate(e))
  C.append(a)
 return C
# Test whether positive symmetric monomial data alone can justify monotonicity.
weak=[];cases=0
for n in range(3,6):
 for d in range(1,13):
  for l in parts(d,n):
   p={e:F(1) for e in set(permutations(l))}
   C=specialize(p,n,F(1,2),d)
   for i in range(1,n):
    a=numerator(C[i-1],C[i],C[i+1]);cases+=1
    v=sum(c*F(2)**k for k,c in enumerate(a))
    if v<0:weak.append({'n':n,'lambda':l,'i':i,'x':2,'N':str(v)});break
   if weak:break
  if weak:break
 if weak:break
# exact shifted-N sufficient invariant on Schur slice (not a new theorem)
coeffchecks=0;negative=[]
for n in range(2,5):
 for d in range(1,7):
  for l in parts(d,n):
   if l[0]==l[-1]:continue
   C=specialize(P(l,n),n,F(1,2),d)
   for i in range(1,n):
    a=shift(numerator(C[i-1],C[i],C[i+1]));coeffchecks+=1
    if any(x<0 for x in a):negative.append({'n':n,'lambda':l,'i':i,'negative_indices':[j for j,x in enumerate(a) if x<0]})
(L/'routes.json').write_text(json.dumps({'schur_determinant_checks':schur,'generic_monomial_checks':cases,'generic_counterexample':weak,'schur_shifted_N_checks':coeffchecks,'negative_shifted_N':negative},indent=2));print((L/'routes.json').read_text())
