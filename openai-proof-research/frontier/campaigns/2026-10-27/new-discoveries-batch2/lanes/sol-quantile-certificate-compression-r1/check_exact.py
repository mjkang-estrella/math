"""Independent standard-library checker: no imports of discovery code or old certificate."""
from fractions import Fraction as Q
from pathlib import Path
import json
L=Path(__file__).parent
S=[[Q(1),Q(13,10),Q(11,5),Q(14,5),Q(29,10)],
   [Q(1,2),Q(9,10),Q(9,10),Q(8,5),Q(9,5)]]
for slopes in S:
 assert all(x>0 for x in slopes)
 assert all(x<=y for x,y in zip(slopes,slopes[1:]))
 assert sum((Q(1,5) for _ in slopes),Q(0))==1
def quant(k,u):
 assert 0<=u<=1
 return sum((s*max(Q(0),min(u-Q(i,5),Q(1,5))) for i,s in enumerate(S[k])),Q(0))
assert [quant(0,Q(i,5)) for i in range(6)]==list(map(Q,['0','1/5','23/50','9/10','73/50','51/25']))
assert [quant(1,Q(i,5)) for i in range(6)]==list(map(Q,['0','1/10','7/25','23/50','39/50','57/50']))
scale=Q(159,2000)
K=list(map(Q,[0,4,10,20,24,38,40]));HV=list(map(Q,[0,-4,2,-8,-4,-18,-16]))
T=list(map(Q,[0,3,7,17,20]));DV=list(map(Q,[2,-1,3,-7,-4]))
def affine(x,knots,values):
 assert knots[0]<=x<=knots[-1]
 for a,b,c,d in zip(knots,knots[1:],values,values[1:]):
  if x<=b:return c+(d-c)*(x-a)/(b-a)
def H(t):return affine(t,K,HV)
def D(t):return affine(t,T,DV)
def h(x):return scale*H(x/scale)
def potential(u):return scale*D((quant(0,u)+quant(1,u))/(2*scale))
cells=[];total=0
for i,(a,b) in enumerate(zip(T,T[1:])):
 for j,(c,d) in enumerate(zip(T,T[1:])):
  if j<i:continue
  points={(a,c),(a,d),(b,c),(b,d)}
  for k in K[1:-1]:
   for x in (a,b):
    if c<=k-x<=d:points.add((x,k-x))
   for y in (c,d):
    if a<=k-y<=b:points.add((k-y,y))
  slack=[D(x)+D(y)-H(x+y) for x,y in points]
  assert min(slack)>=0
  cells.append({'i':i+1,'j':j+1,'vertices':len(points),'minimum_scaled_slack':str(min(slack))})
  total+=len(points)
# Independently split every affine source piece at quantile and payoff breaks.
p=[17,16,15,14,13,11,10,9,7,5,3,1,0,18,19,12,8,6,4,2]
assert sorted(p)==list(range(20))
integrals=[];subpieces=0
for i,j in enumerate(p):
 a,b=Q(i,20),Q(i+1,20);shift=Q(j-i,20)
 points={a,b}
 for v in [Q(k,5) for k in range(1,5)]:
  for x in [v,v-shift]:
   if a<x<b:points.add(x)
 def f(u):return quant(0,u)+quant(1,u+shift)
 base=sorted(points)
 for lo,hi in zip(base,base[1:]):
  flo,fhi=f(lo),f(hi)
  assert fhi>flo
  for v in K[1:-1]:
   z=scale*v
   if flo<z<fhi:points.add(lo+(hi-lo)*(z-flo)/(fhi-flo))
 points=sorted(points);subpieces+=len(points)-1
 integrals.append(sum(((hi-lo)*(h(f(lo))+h(f(hi)))/2 for lo,hi in zip(points,points[1:])),Q(0)))
A=sum(integrals,Q(0))
points={Q(k,5) for k in range(6)}
for lo,hi in zip(sorted(points),sorted(points)[1:]):
 rl=(quant(0,lo)+quant(1,lo))/2;rh=(quant(0,hi)+quant(1,hi))/2
 for v in T[1:-1]:
  z=scale*v
  if rl<z<rh:points.add(lo+(hi-lo)*(z-rl)/(rh-rl))
points=sorted(points)
B=sum(((hi-lo)*(potential(lo)+potential(hi)) for lo,hi in zip(points,points[1:])),Q(0))
assert A==Q(-68997954679,659497410000)
assert B==Q(-83231059,641080000)
assert A-B==Q(100817889097,3999532680000)>0
out={'status':'PASS','arithmetic':'Fraction only; no optimizer, tolerances, or old data imports',
 'symmetric_rectangle_checks':cells,'total_vertex_checks':total,'source_affine_subpieces':subpieces,
 'source_interval_integrals':list(map(str,integrals)),
 'target_u_breakpoints':list(map(str,points)),'source_expectation':str(A),'universal_target_upper':str(B),'strict_gap':str(A-B),'rounding_error':'0'}
(L/'exact-check.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
