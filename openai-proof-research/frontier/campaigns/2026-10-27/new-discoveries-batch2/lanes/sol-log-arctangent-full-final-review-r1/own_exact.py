import resource,os,json,math
from fractions import Fraction as F
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(35,)*2)
# Independent recurrence on exponential polynomials: key (frequency in Q(sqrt17), degree).
def Q(a=0,b=0):return (F(a),F(b))
def add(x,y):return (x[0]+y[0],x[1]+y[1])
def neg(x):return (-x[0],-x[1])
def mul(x,y):return (x[0]*y[0]+17*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def power(x,n):
 r=Q(1)
 for _ in range(n):r=mul(r,x)
 return r
def plus(*args):
 r={}
 for p in args:
  for k,v in p.items():r[k]=add(r.get(k,Q()),v)
 return {k:v for k,v in r.items() if v!=Q()}
def scale(p,c):return {k:mul(v,c) for k,v in p.items() if mul(v,c)!=Q()}
def prod(p,q):
 r={}
 for (l,j),v in p.items():
  for (m,k),w in q.items():
   key=(add(l,m),j+k);r[key]=add(r.get(key,Q()),mul(v,w))
 return plus(r)
def D(p):
 r={}
 for (l,j),v in p.items():
  r=plus(r,{(l,j):mul(l,v)})
  if j:r=plus(r,{(l,j-1):mul(Q(j),v)})
 return r
def hyp(l,odd=False):return {(l,0):Q(F(1,2)),(neg(l),0):Q(-F(1,2) if odd else F(1,2))}
def sh(l):return hyp(l,True)
def ch(l):return hyp(l)
t={(Q(),1):Q(1)};one={(Q(),0):Q(1)}
a=Q(F(5,2),F(1,2));b=Q(F(5,2),-F(1,2));d=Q(0,1)
B=prod(prod(sh(Q(1)),sh(a)),sh(b))
# A/B = coth(t) - (alpha coth(alpha t)-beta coth(beta t))/d
A=plus(prod(prod(ch(Q(1)),sh(a)),sh(b)),scale(prod(sh(Q(1)),plus(scale(prod(ch(a),sh(b)),a),scale(prod(sh(a),ch(b)),neg(b)))),Q(0,-F(1,17))))
assert A==scale(plus(ch(Q(4)),scale(prod(ch(Q(1)),ch(d)),Q(-1)),scale(prod(sh(Q(1)),sh(d)),Q(0,F(5,17)))),Q(F(1,2)))
U=plus(prod(D(B),A),scale(prod(B,D(A)),Q(-1)),scale(prod(A,A),Q(-1)))
V=scale(prod(B,A),Q(-4));E=plus(U,scale(prod(prod(t,t),U),Q(2)),prod(t,V))
assert U[(Q(),0)]==Q(-F(87,68));assert all(k[0]!=Q() for k in V)
freq=[Q(7,1),Q(2,2),Q(10),Q(5,1),Q(0,2),Q(8),Q(3,1),Q(-2,2),Q(7,-1),Q(2),Q(-3,1),Q(5,-1)]
def lower(x):return x[0]+x[1]*(F(41,10) if x[1]>=0 else F(21,5))
assert F(41,10)**2<17<F(21,5)**2
assert all(lower(add(x,neg(y)))>0 for x,y in zip(freq,freq[1:]));assert lower(freq[-1])>0
assert set(k[0] for k in U)==set(freq+[neg(x) for x in freq]+[Q()])
sums=[Q(),Q(),Q()];rows=[];target={}
for l in freq:
 u=U[(l,0)];v=V[(l,0)];l22=power(l,22)
 cs=[mul(l22,add(add(mul(u,power(l,2)),mul(Q(24),mul(v,l))),mul(Q(1104),u))),mul(l22,add(mul(v,l),mul(Q(94),u))),mul(l22,mul(Q(2),u))]
 sums=[add(x,y) for x,y in zip(sums,cs)];assert all(lower(x)>0 for x in sums)
 rows.append({'frequency':l,'coefficients':cs,'prefix':sums,'lower':[lower(x) for x in sums]})
 for sign in [1,-1]:
  f=mul(Q(sign),l);target[(f,0)]=cs[0];target[(f,1)]=mul(Q(sign),mul(l,add(cs[1],cs[2])));target[(f,2)]=mul(power(l,2),cs[2])
expected={10:37847040,12:19891322880,14:5550283554816,16:1162696473968640,18:206947471161556992,20:33226670114812723200,22:4978839848478924865536}
jets=[];p=E
for n in range(24):
 j=Q()
 for (l,k),v in p.items():
  if k==0:j=add(j,v)
 assert j==Q(expected.get(n,0)),(n,j);jets.append(j);p=D(p)
assert p==plus(target)
assert sums==list(map(Q,[355707128874106034847744,46479400985961399582720,1463704104369024663552]))
# An omitted +2u in the linear coefficient changes D24.
wrong=dict(target);l=freq[0];wrong[(l,1)]=mul(l,rows[0]['coefficients'][1]);assert p!=wrong
Path('own-exact-results.json').write_text(json.dumps({'rows':rows,'jets':jets,'derivative24_identity':True,'mutation_rejected':True,'limits':{'AS':512*1024**2,'CPU':35,'wall':45,'BLAS':1}},default=str,indent=2))
print('PASS: independently reconstructed A,B,U,V,E; 36 prefixes; 24 jets; recurrent D24; final sums; mutation rejection')
