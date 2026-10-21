"""Small exact diagnostics; neither full proof nor mathematical gate. Read-only."""
import json,itertools

def add(a,b): return a^b

def mul(a,b):
 c=0
 while b:
  if b&1:c^=a
  b>>=1;a<<=1
  if a&4:a^=7
 return c

def pmul(a,b):return tuple(mul(a[0],b[0]) if i==0 else (mul(a[0],b[1])^mul(a[1],b[0])) if i==1 else (mul(a[0],b[2])^mul(a[1],b[1])^mul(a[2],b[0])) for i in range(3))
A=list(itertools.product(range(4),repeat=3));one=(1,0,0)
U=[a for a in A if any(pmul(a,b)==one for b in A)]
P=[a for a in U if a[0]==1]
assert len(U)==48 and len(P)==16
assert all(pmul(a,b) in P for a in P for b in P)
assert all(pmul(pmul(a,a),pmul(a,a))==one for a in P)
assert (1,1,0) in U and (1,0,1) in U
cases=[]
for p,level in [(2,1),(2,2),(2,3),(3,1),(3,2)]:
 mod=p**level;V=list(itertools.product(range(mod),repeat=2));mods=set()
 for x,y in V:
  W=frozenset(((a+b*x)%mod,(a+b*y)%mod) for a in range(mod) for b in range(mod))
  mods.add(W)
 good=[]
 for W in mods:
  if all(((a*c)%mod,(b*d)%mod) in W for a,b in W for c,d in W):good.append(W)
 expected={frozenset((a,b) for a,b in V if (a-b)%(p**t)==0) for t in range(level+1)}
 assert set(good)==expected
 cases.append({'p':p,'level':level,'unital_subrings':len(good),'sizes':sorted(map(len,good))})
print(json.dumps({'finite_order_cases':cases,'unit_group_example':{'field':4,'algebra_dimension':3,'unit_group_order':len(U),'sylow_2_order':len(P),'principal_units_exponent_divides':4,'projective_dimension_divisibility_fails':3%len(P)!=0},'scope':'finite diagnostics only; no mathematical gate'},indent=2))
