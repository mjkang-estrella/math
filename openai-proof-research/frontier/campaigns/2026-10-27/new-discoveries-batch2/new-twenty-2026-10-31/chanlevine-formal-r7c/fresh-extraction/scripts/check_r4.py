"""Independent exact checks of new generic identities in Z[z]/(z^e-1)[X]."""
import json
for e in range(1,11):
 def add(a,b):
  c=dict(a)
  for k,v in b.items(): c[k]=c.get(k,0)+v
  return {k:v for k,v in c.items() if v}
 def mul(a,b):
  c={}
  for (i,j),v in a.items():
   for (k,l),w in b.items():
    t=(i+k,(j+l)%e); c[t]=c.get(t,0)+v*w
  return {k:v for k,v in c.items() if v}
 def mm(a,b):
  return [[add(mul(a[i][0],b[0][j]),mul(a[i][1],b[1][j])) for j in range(2)] for i in range(2)]
 one={(0,0):1}; z={(0,1%e):1}; zero={}
 a=[[one,zero],[zero,one]]
 for k in range(e):
  g=add(one,{(1,k%e):-1})
  b=[[add(one,z),{t:-v for t,v in mul(z,g).items()}],[g,zero]]
  a=mm(a,b)
 t=add(a[0][0],a[1][1]); shifted={}
 for (i,j),v in t.items():
  k=(i,(j+i)%e);shifted[k]=shifted.get(k,0)+v
 shifted={k:v for k,v in shifted.items() if v}
 assert shifted==t,(e,'cyclic invariance')
 assert all(i<=e for i,j in t),(e,'degree')
 assert {j:v for (i,j),v in t.items() if i==0}=={0:2},(e,'constant')
 print(json.dumps({'e':e,'degree_constant_invariance':'PASS'}))
print('10 exact group-ring cases; diagnostics only')
