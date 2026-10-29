exec(open(__file__.replace('route.py','check.py')).read().split('E=(O,Z,O)')[0])
from itertools import product
import random
states=[]
for c0,c1,h0,h1 in product(range(1,7),repeat=4):
 if c0<h0 or c1<h1:continue
 for d in [(0,), (1,1),(1,2),(2,1),(3,3),(6,1),(1,6)]:
  a=((c0,c1),d,(h0,h1))
  if lc(add(a[0],mul(T,a[2]))):states.append(a)
rng=random.Random(96);failure=None
for _ in range(20000):
 a=rng.choice(states);b=rng.choice(states)
 for op in ['S','P']:
  out=comp(a,b,op);u=add(out[0],mul(T,out[2]))
  if any(not lc(z) for z in out):
   failure=dict(input1=a,input2=b,op=op,output=out,U=u,negative_defects=[(j,u[j]**2-u[j-1]*u[j+1]) for j in range(1,len(u)-1) if u[j]**2<u[j-1]*u[j+1]]);break
 if failure:break
assert failure is not None
for a in [failure['input1'],failure['input2']]:
 assert all(lc(p) for p in a);assert lc(add(a[0],mul(T,a[2])))
 assert all(cross(a[i],a[j],k)>=0 for i,j in [(0,1),(0,2),(1,2)] for k in range(4))
 assert all(coeff(a[0],k)>=coeff(a[2],k) for k in range(4))
# Independent finite-field direct pair-polynomial evaluation, not class equality from counts.
def ev(p,s):return sum(a*s**i for i,a in enumerate(p))
def direct(expr,values,q):
 if expr=='E':return 1,next(values)
 op,a,b=expr;x,y=direct(a,values,q);z,w=direct(b,values,q)
 return ((x*z)%q,(y*z+x*w)%q) if op=='S' else ((x*w+y*z)%q,(y*w)%q)
def calc(expr):return (O,Z,O) if expr=='E' else comp(calc(expr[1]),calc(expr[2]),expr[0])
def size(e):return 1 if e=='E' else size(e[1])+size(e[2])
exprs=['E',('S','E','E'),('P','E','E'),('P',('S','E','E'),('S','E','E')),('S',('P','E','E'),('P','E','E')),('P',('S',('P','E','E'),'E'),'E')]
finite=[]
for expr in exprs:
 a=calc(expr)
 for q in [2,3,5]:
  obs=[0,0,0,0]
  for v in product(range(q),repeat=size(expr)):
   x,y=direct(expr,iter(v),q)
   if x and not y:obs[0]+=1
   if y and not x:obs[1]+=1
   if x and y:obs[2]+=1
   if x==y and x!=0:obs[3]+=1
  expected=[ev(a[0],q-2),ev(a[1],q-2),(q-1)*ev(a[2],q-2),ev(a[2],q-2)]
  assert obs==expected,(expr,q,obs,expected)
  finite.append(dict(expression=expr,q=q,counts=obs))
(P/'route-results.json').write_text(json.dumps(dict(cone_obstruction=failure,finite_field_checks=finite,source_result=False),indent=2));print(json.dumps(failure,indent=2));print('direct checks',len(finite))
