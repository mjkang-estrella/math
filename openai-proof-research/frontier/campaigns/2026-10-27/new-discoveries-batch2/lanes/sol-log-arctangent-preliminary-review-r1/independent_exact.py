#!/usr/bin/env python3
"""Independent construction from the coth numerator, in Q[d][t,exp(t/2),exp(dt/2)], d²=17.
No candidate code or precomputed terms imported. Output is an ordinary exact certificate,
not a proof-assistant certificate. Run with Python standard library only.
"""
import os,resource,json,math
from fractions import Fraction as F
from pathlib import Path
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(40,40))
Z=(F(0),F(0)); ONE=(F(1),F(0)); d=(F(0),F(1))
def q(a=0,b=0):return(F(a),F(b))
def add(x,y):return(x[0]+y[0],x[1]+y[1])
def neg(x):return(-x[0],-x[1])
def mul(x,y):return(x[0]*y[0]+17*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def scale(x,a):return(x[0]*a,x[1]*a)
def sign(x):
 a,b=x
 if not b:return (a>0)-(a<0)
 if not a:return (b>0)-(b<0)
 if a>0 and b>0:return 1
 if a<0 and b<0:return -1
 s=(a*a>17*b*b)-(a*a<17*b*b)
 return s if a>0 else -s
def absq(x):return x if sign(x)>=0 else neg(x)
def gt(x,y):return sign(add(x,neg(y)))>0
# Keys (polynomial t degree, rational exponent, radical exponent).
def clean(p):return {k:v for k,v in p.items() if v!=Z}
def plus(*ps):
 out={}
 for p in ps:
  for k,v in p.items():out[k]=add(out.get(k,Z),v)
 return clean(out)
def times(p,r):
 out={}
 for (i,a,b),v in p.items():
  for (j,c,e),w in r.items():
   k=(i+j,a+c,b+e);out[k]=add(out.get(k,Z),mul(v,w))
 return clean(out)
def sm(p,x):return clean({k:mul(v,x) for k,v in p.items()})
def diff(p):
 out={}
 for (i,a,b),v in p.items():
  out=plus(out,{(i,a,b):mul(v,q(a,b))})
  if i:out=plus(out,{(i-1,a,b):scale(v,i)})
 return out
def hyp(a,b,odd=False):return {(0,F(a),F(b)):q(F(1,2)),(0,-F(a),-F(b)):q(F(-1 if odd else 1,2))}
sh=lambda a,b=0:hyp(a,b,True)
ch=lambda a,b=0:hyp(a,b)
alpha=q(F(5,2),F(1,2));beta=q(F(5,2),F(-1,2))
sa,ca=sh(F(5,2),F(1,2)),ch(F(5,2),F(1,2))
sb,cb=sh(F(5,2),F(-1,2)),ch(F(5,2),F(-1,2))
B=times(sh(1),times(sa,sb))
A=plus(times(ch(1),times(sa,sb)),sm(times(sh(1),plus(sm(times(ca,sb),alpha),sm(times(sa,cb),neg(beta)))),q(0,F(-1,17))))
# Compare against displayed A and B only after independent construction.
Adis=sm(plus(ch(4),sm(times(ch(1),ch(0,1)),q(-1)),sm(times(sh(1),sh(0,1)),q(0,F(5,17)))),q(F(1,2)))
Bdis=sm(times(sh(1),plus(ch(5),sm(ch(0,1),q(-1)))),q(F(1,2)))
assert A==Adis and B==Bdis
T={(0,F(0),F(0)):ONE,(2,F(0),F(0)):q(2)}
D=times(T,A)
E=plus(times(diff(B),D),sm(times(B,diff(D)),q(-1)),sm(times(T,times(A,A)),q(-1)))
# This is the numerator of (B/D)' - 1/(1+2t²), directly by quotient rule.
# parity of E and extraction of U,V
assert all(E.get((i,-a,-b),Z)==scale(v,(-1)**i) for (i,a,b),v in E.items())
U={(a,b):v for (i,a,b),v in E.items() if i==0}
V={(a,b):v for (i,a,b),v in E.items() if i==1}
assert all(E.get((2,a,b),Z)==scale(v,2) for (a,b),v in U.items())
assert all(i in (0,1,2) for i,a,b in E)
powers={k:ONE for k in {(a,b) for i,a,b in E}}
values=[]
# Compute moments for each polynomial degree separately, no convolution of A_n,B_n.
moments=[]
for n in range(300):
 moments.append([Z for _ in range(3)])
 for (i,a,b),v in E.items():moments[-1][i]=add(moments[-1][i],mul(v,powers[a,b]))
 powers={k:mul(v,q(*k)) for k,v in powers.items()}
for n in range(300):
 v=moments[n][0]
 if n>=1:v=add(v,scale(moments[n-1][1],n))
 if n>=2:v=add(v,scale(moments[n-2][2],n*(n-1)))
 assert v[1]==0 and v[0].denominator==1
 values.append(int(v[0]))
 assert v==Z if n<10 or n%2 else sign(v)>0
assert values[10:17:2]==[37847040,19891322880,5550283554816,1162696473968640]
L=q(7,1); R=q(F(41,4));u=q(F(-85,544),F(21,544));v=q(F(17,272),F(-5,272))
assert U[7,1]==u and U[-7,-1]==u and V[7,1]==v and V[-7,-1]==neg(v)
assert gt(u,q(F(1,1000))) and gt(v,q(F(-1,50))) and gt(L,q(11)) and gt(q(12),L)
for a,b in set(U)|set(V):
 if (a,b) not in [(7,1),(-7,-1)]:assert gt(R,absq(q(a,b)))
lu=Z;lv=Z
for z in U.values():lu=add(lu,absq(z))
for z in V.values():lv=add(lv,absq(z))
assert gt(q(10),lu) and gt(q(10),lv)
assert 44**298>11000*41**298
# For all n>=300: dominant bracket >= n²/1000, remainder <22n²R^(n-2).
# Dominant residual n(n-242)/1000 >=0. Remainder divided by n² is
# 20+(10R-20)/n+10R²/n², strictly decreasing for n>0; test n=300.
rr=F(41,4)
assert 20+(10*rr-20)/300+10*rr**2/300**2<22
# A positivity constants: d in (4,17/4), (16/13)^2>9/8.
assert gt(d,q(4)) and gt(q(F(17,4)),d) and F(16,13)**2>F(9,8)
def enc(z):return [str(z[0]),str(z[1])]
def terms(p):return [{'key':[str(x) for x in k],'coefficient':enc(v)} for k,v in sorted(p.items())]
out={'status':'PASS exact ordinary arithmetic only','limits':{'address_space':512*1024**2,'cpu_seconds':40,'threads':1},'A':terms(A),'B':terms(B),'E':terms(E),'derivatives_0_through_299':values,'U_l1':enc(lu),'V_l1':enc(lv),'dominant_U':enc(u),'dominant_V':enc(v),'tail_radius':'41/4','all_order_tail':'analytic argument in review.md; finite identities and rational bounds asserted here','candidate_code_imported':False}
Path(__file__).with_name('independent-evidence.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['status','limits','U_l1','V_l1','dominant_U','dominant_V']}))
