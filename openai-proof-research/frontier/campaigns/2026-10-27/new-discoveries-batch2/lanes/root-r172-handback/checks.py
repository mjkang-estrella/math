import json,itertools,math
from pathlib import Path
L=Path(__file__).resolve().parent
# Exact GF(9)=F_3[t]/(t^2+1); elements encoded a+3b.
def add(x,y):return ((x%3+y%3)%3)+3*((x//3+y//3)%3)
def neg(x):return (-x%3)+3*(-(x//3)%3)
def sub(x,y):return add(x,neg(y))
def mul(x,y):
 a,b=x%3,x//3;c,d=y%3,y//3
 return (a*c+2*b*d)%3+3*((a*d+b*c)%3)
def power(x,n):
 r=1
 while n:
  if n%2:r=mul(r,x)
  x=mul(x,x);n//=2
 return r
def inv(x):assert x;return power(x,7)
def point(x):return (1,0) if x is None else (x,1)
def det(x,y):return sub(mul(x[0],y[1]),mul(x[1],y[0]))
def cr(x,z,a,b):return mul(mul(det(x,b),det(z,a)),inv(mul(det(x,a),det(z,b))))
def degree(X):
 vals=[cr(*q) for q in itertools.permutations(map(point,X),4)]
 return 1 if all(power(x,3)==x for x in vals) else 2
A=[None,0,1,2];B=[None,0,3,6];X=[None,0,1,2,3,6]
assert degree(A)==degree(B)==1 and degree(X)==2
# Mobius y -> 1/(y-(1+t)) removes infinity, with pole outside X.
def transform(x):return 0 if x is None else inv(sub(x,4))
Y=list(map(transform,X));assert len(set(Y))==6
assert degree(list(map(transform,A)))==degree(list(map(transform,B)))==1
assert degree(Y)==2
identities=0
for q in itertools.permutations(X,4):
 assert cr(*map(point,q))==cr(*map(point,map(transform,q)));identities+=1
# Every four-helper local relative-degree condition fails somewhere: this
# is a failed generalized lcm bridge, NOT a source counterexample.
fail=[]
for H in itertools.combinations(Y,4):
 for i in set(Y)-set(H):
  if degree(list(H)+[i])<2*degree(H):fail.append([H,i])
assert fail
# Independently reconstruct the published EHS Example4.2 ideal's antichain.
G=[(50,0),(40,10),(39,34),(38,35),(37,36),(36,37),(35,38),(34,39),(10,40),(0,50)]
def minimal(T):return sorted(p for p in set(T) if not any(q!=p and q[0]<=p[0] and q[1]<=p[1] for q in set(T)))
P=[(a+c,b+d) for a,b in G for c,d in G];M=minimal(P)
assert len(minimal(G))==10 and M==[(0,100),(10,90),(20,80),(40,60),(50,50),(60,40),(80,20),(90,10),(100,0)]
j=dict(gf9_overlap=dict(A=A,B=B,union=X,finite_union=Y,degrees=[1,1,2],mobius_quadruples=identities,failed_local_repair_pairs=len(fail),scope='Exact obstruction to unqualified lcm-extension only; no valid repair code constructed.'),published_monomial=dict(generators=G,square_generators=M,mu=[10,9],ordered_products=100,scope='Known 2018 counterexample, no novelty credit.'))
(L/'checks.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(j))
