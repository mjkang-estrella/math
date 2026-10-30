"""Exact bounded checks of a PRIOR PUBLIC certificate, not discovery evidence."""
from fractions import Fraction as F
import json
from pathlib import Path
L=Path(__file__).resolve().parent
def add(a,b):
 c=[F(0)]*max(len(a),len(b))
 for i,v in enumerate(a):c[i]+=v
 for i,v in enumerate(b):c[i]+=v
 return trim(c)
def trim(c):
 while len(c)>1 and c[-1]==0:c.pop()
 return c
def scale(a,s):return trim([x*s for x in a])
def mul(a,b):
 c=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return trim(c)
def ev(a,x):
 v=F(0)
 for y in reversed(a):v=v*x+y
 return v
P=[F(-137),0,F(6831),0,F(-41568),0,F(38656)]
one=[F(137)];line=[F(-1078),F(4860)]
certs=[
 (add(one,scale(P,-1)),mul([1,0,-16],[274,0,-2447,0,2416])),
 (add(one,P),mul([0,0,1],[6831,0,-41568,0,38656])),
 (add(line,scale(P,-1)),mul(mul([1,-1],[-1,4]),[941,-155,2292,12080,9664])),
 (add(line,P),mul(mul([-3,4],[-3,4]),[-135,180,1479,3624,2416])),
 ([-135,180,1479,3624,2416],add([F(137,2)],mul([F(-1,4),1],[814,2536,4228,2416])))
]
assert all(trim(a)==trim(b) for a,b in certs)
bounds=[F(274)-F(2447,16),F(6831)-F(41568,16),F(941)-155,F(137,2)]
assert min(bounds)>0
contacts=[F(1),F(3,4),F(1,4),F(0),F(-1,4),F(-3,4),F(-1)]
vals=[]
for i,x in enumerate(contacts):
 mu=max(F(1),(4860*abs(x)-1078)/137)
 y=ev(P,x)/137;assert y==(-1)**i*mu;vals.append(str(y))
T=[[F(1)],[0,F(1)]]
for k in range(2,7):T.append(add(mul([0,2],T[-1]),scale(T[-2],-1)))
co=[F(-459,274),0,F(1503,274),0,F(2052,137),0,F(1208,137)]
q=[F(0)]
for a,t in zip(co,T):q=add(q,scale(t,a))
assert q==scale(P,F(1,137))
assert co[0]<0 and co[6]>0
# Positive leading coefficients of T_k give linear independence by top degree.
assert all(t[-1]>0 and len(t)==k+1 for k,t in enumerate(T))
out=dict(certificate='prior public SnakeChebyshevExpansionRefutation, not new',polynomial_identities=len(certs),strict_interval_lower_bounds=list(map(str,bounds)),contacts=vals,chebyshev_coefficients=list(map(str,co)),orientation_obstruction=True,conclusion='Exact identities plus the written interval inequalities cover every real x in [-1,1]; no numerical mesh is used.')
print(json.dumps(out,indent=2))
