#!/usr/bin/env python3
"""Bounded exact polynomial-matrix diagnostics, not a homology proof."""
import json,random
rng=random.Random(17780);checks=0
for q in (3,5,7):
 for n in (3,4):
  for m in (2,3,4):
   L=4*m+1
   zero=lambda:[0]*L
   def add(a,b):return [(x+y)%q for x,y in zip(a,b)]
   def mul(a,b):
    c=zero()
    for i,x in enumerate(a):
     for j,y in enumerate(b):
      if i+j<L:c[i+j]=(c[i+j]+x*y)%q
    return c
   def eye():
    z=[[zero() for _ in range(n)]for _ in range(n)]
    for i in range(n):z[i][i][0]=1
    return z
   def mm(a,b):
    c=[[zero()for _ in range(n)]for _ in range(n)]
    for i in range(n):
     for j in range(n):
      for k in range(n):c[i][j]=add(c[i][j],mul(a[i][k],b[k][j]))
    return c
   def rho(a):
    z=eye()
    for j in range(1,n):z[0][j][m:2*m]=a[0][j][m:2*m]
    return z
   def gamma():
    a=eye()
    for _ in range(5):
     i,j=rng.sample(range(n),2);b=eye()
     b[i][j][m:2*m]=[rng.randrange(q)for _ in range(m)]
     a=mm(a,b)
    return a
   for _ in range(12):
    a,b=gamma(),gamma();assert rho(mm(a,b))==mm(rho(a),rho(b));checks+=1
    assert rho(rho(a))==rho(a);checks+=1
    e=eye()
    for j in range(1,n):e[0][j][m:2*m]=[rng.randrange(q)for _ in range(m)]
    assert rho(e)==e;checks+=1
# Explicit wrong-formula control: retaining degree2m destroys additivity.
a,b=eye(),eye();a[0][1][m]=1;b[1][2][m]=1
assert mm(a,b)[0][2][2*m]==1 and a[0][2][2*m]+b[0][2][2*m]==0
print(json.dumps({'status':'PASS','exact_checks':checks,'wrong_cutoff_control':'degree2m cross-term detected','limits':'Finite truncated polynomial matrices only; no Betti computation, upper bound, infinite-family proof or contribution verdict.'},indent=2))
