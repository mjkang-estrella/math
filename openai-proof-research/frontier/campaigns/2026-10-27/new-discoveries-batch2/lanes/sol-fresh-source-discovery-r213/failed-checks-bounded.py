import json, sympy as s
x=s.Symbol('x')
def D(L,a):
 b=[0]*(len(a)+1)
 for j,v in enumerate(a):b[j]+=(j+1)*v;b[j+1]+=(L-j)*v
 while len(b)>1 and b[-1]==0:b.pop()
 return b
def add(a,b):return [(a[j] if j<len(a) else 0)+(b[j] if j<len(b) else 0) for j in range(max(len(a),len(b)))]
def poly(a):return s.Poly.from_list(a[::-1],x,domain=s.ZZ)
A={(1,0):[1,1],(1,1):[1]}
for k in range(2,10):
 for i in range(k+1):
  v=[0]
  if i<k:v=D(3*k-i-3,A[k-1,i])
  if i>0:v=add(v,A[k-1,i-1])
  A[k,i]=D(3*k-i-2,v)
assert A[3,1]==[3,114,501,436,66]
rows=[]
for k in range(1,10):
 for i in range(k+1):
  p=poly(A[k,i]);c=p.count_roots(-s.oo,0)
  assert c==p.degree() and s.gcd(p,p.diff()).degree()==0
  rows.append([k,i,p.degree(),c])
# Exact interlacing via Sturm-isolated rational intervals of g and signs of f.
comparisons=[]
for k in range(5,10):
 f=poly(D(3*k-7,A[k-1,4]));g=poly(A[k-2,0]);assert f.degree()+1==g.degree()
 intervals=g.intervals(eps=s.Rational(1,10)**12)
 signs=[];overlap=False
 for (a,b),m in intervals:
  assert m==1
  if f.count_roots(a,b):overlap=True
  signs.append(s.sign(f.eval(a)))
 passed=not overlap and all(signs[j]*signs[j+1]==-1 for j in range(len(signs)-1))
 comparisons.append(dict(k=k,interlaces=bool(passed),signs=list(map(int,signs))))
# Independent explicit insertion of actual words up to k=3.
from collections import Counter
from math import comb, factorial
words={(0,()):[()]}
for k in range(1,4):
 for bits in range(1<<k):
  S=tuple(j+1 for j in range(k) if (bits>>j)&1)
  prev=tuple(j for j in S if j<k)
  old=words[k-1,prev];new=[]
  for w in old:
   ws=[w] if k in S else [w[:j]+(2*k-1,)+w[j:] for j in range(len(w)+1)]
   for w1 in ws:
    new.extend(w1[:j]+(2*k,2*k)+w1[j:] for j in range(len(w1)+1))
  words[k,S]=new
 for i in range(k+1):
  c=Counter(sum(w[j]>w[j+1] for j in range(len(w)-1)) for (n,S),ws in words.items() if n==k and len(S)==i for w in ws)
  assert [c[j] for j in range(max(c)+1)]==A[k,i]
for (k,i),v in A.items():
 assert sum(v)*3**(k-i)*2**i*factorial(i)*factorial(k-i)==factorial(3*k-i)
# Exact obstruction to stability of the natural deletion-marked bivariate polynomial.
assert s.discriminant(poly(add(add(A[2,0],[-2*v for v in A[2,1]]),[4*v for v in A[2,2]])).as_expr(),x)==-4192
# Nonnegative sums of real-rooted positive-coefficient polynomials need not be real-rooted.
p=(x+1)*(x+2);q=(x+10)*(x+11);assert s.discriminant(p+q,x)==-320
print(json.dumps(dict(real_root_checks=rows,remark1_comparisons=comparisons,generic_sum_discriminant=-320),sort_keys=True))
