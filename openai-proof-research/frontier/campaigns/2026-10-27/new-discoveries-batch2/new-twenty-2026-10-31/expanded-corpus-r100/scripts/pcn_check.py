import json,math
from sympy.polys.galoistools import gf_irreducible_p
from sympy.polys.domains import ZZ
p=11;q=p**7
assert gf_irreducible_p([1,0,0,0,0,0,1,4],p,ZZ)
def mul(x,y):
 a=[];b=[]
 for i in range(7):a.append(x%p);x//=p;b.append(y%p);y//=p
 w=[0]*13
 for i in range(7):
  for j in range(7):w[i+j]+=a[i]*b[j]
 for i in range(12,6,-1):w[i-7]-=4*w[i];w[i-6]-=w[i]
 return sum((w[i]%p)*p**i for i in range(7))
def pw(a,d):
 r=1
 while d:
  if d&1:r=mul(r,a)
  a=mul(a,a);d//=2
 return r
def add(x,y):
 return sum(((x//p**i+y//p**i)%p)*p**i for i in range(7))
def F(x,d):return add(pw(x,d),pw(x-x%p+(x%p+1)%p,d))
base=json.load(open('outputs/pcn.json'));ref={t['d']:t for t in json.load(open('outputs/pcn-refine.json'))['trials']};counts={}
for t in base['trials']:
 if t['rejection'] is None:t=ref[t['d']]
 assert t['rejection'] is not None
 counts[t['rejection']]=counts.get(t['rejection'],0)+1
 if 'collision' in t['rejection']:assert t['x']!=t['y'] and F(t['x'],t['d'])==F(t['y'],t['d'])==t['value']
 else:assert math.gcd(t['d'],q-1)>1
out=dict(field_irreducible=True,all_stored_collisions_scalar_recomputed=True,total=len(base['trials']),counts=counts)
print(out);json.dump(out,open('outputs/pcn-crosscheck.json','w'),indent=2)
