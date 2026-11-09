import os,resource,json
os.environ['OMP_NUM_THREADS']='1';os.environ['OPENBLAS_NUM_THREADS']='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(40,)*2)
from fractions import Fraction as F
from pathlib import Path
# pair field Q(sqrt17)
def add(a,b):return(a[0]+b[0],a[1]+b[1])
def neg(a):return(-a[0],-a[1])
def mul(a,b):return(a[0]*b[0]+17*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def scale(a,x):return(a[0]*x,a[1]*x)
z=(F(0),F(0));one=(F(1),F(0))
def plus(A,B):
 R=A.copy()
 for k,v in B.items():R[k]=add(R.get(k,z),v)
 return {k:v for k,v in R.items() if v!=z}
def sm(A,x):return {k:scale(v,x) for k,v in A.items()}
def times(A,B):
 R={}
 for k,v in A.items():
  for l,w in B.items():
   u=add(k,l);R[u]=add(R.get(u,z),mul(v,w))
 return {k:v for k,v in R.items() if v!=z}
def C(k):return {k:scale(one,F(1,2)),neg(k):scale(one,F(1,2))}
def S(k):return {k:scale(one,F(1,2)),neg(k):scale(one,F(-1,2))}
def der(A):return {k:mul(k,v) for k,v in A.items()}
def cm(A,x):return {k:mul(v,x) for k,v in A.items()}
d=(F(0),F(1));a=(F(1),F(0));four=(F(4),F(0));five=(F(5),F(0))
A=sm(plus(plus(C(four),sm(times(C(a),C(d)),-1)),cm(times(S(a),S(d)),(F(0),F(5,17)))),F(1,2))
B=sm(times(S(a),plus(C(five),sm(C(d),-1))),F(1,2))
U=plus(plus(times(der(B),A),sm(times(B,der(A)),-1)),sm(times(A,A),-1));V=sm(times(B,A),-4)
# E=U+tV+2t²U, ordinary power coefficients multiplied by n!.
powers={}
for k in set(U)|set(V):
 powers[k]=[one]
 for n in range(300):powers[k].append(mul(powers[k][-1],k))
def moment(P,n):
 R=z
 for k,v in P.items():
  w=powers[k][n]
  R=add(R,mul(v,w))
 return R
def positive(k):
 a,b=k
 if a>=0 and b>=0:return a+b>0
 if a<=0 and b<=0:return False
 return a*a>17*b*b if a>0 else 17*b*b>a*a
rows=[]
for n in range(0,300,2):
 e=moment(U,n)
 if n>=1:e=add(e,scale(moment(V,n-1),n))
 if n>=2:e=add(e,scale(moment(U,n-2),2*n*(n-1)))
 rows.append({'n':n,'rational':str(e[0]),'sqrt17':str(e[1]),'sign':0 if e==z else 1 if positive(e) else -1})
out={'meaning':'Exact finite coefficient certificate; tail bounds asserted below and explained in PROOF.md','coefficients':rows,'U_terms':len(U),'V_terms':len(V)}
Path(__file__).with_name('expchecks.json').write_text(json.dumps(out,indent=2));print('PASS exact coefficients through 298')

# Exact all-order tail certificate.
L=(F(7),F(1));u=U[L];v=V[L]
assert positive(add(u,(-F(1,1000),F(0))))
assert positive(add(v,(F(1,50),F(0))))
assert positive(add((F(12),F(0)),neg(L)))
assert positive(add(L,(-F(11),F(0))))
for P in [U,V]:
 total=z
 for k,w in P.items():total=add(total,w if positive(w) else neg(w))
 assert positive(add((F(10),F(0)),neg(total)))
for k in (set(U)|set(V))-{L,neg(L)}:
 if positive(k):assert positive(add((F(41,4),F(0)),neg(k)))
 else:assert positive(add((F(41,4),F(0)),k))
assert F(44,41)**298>11000
assert all(r['sign']==0 for r in rows[:5])
assert all(r['sign']==1 for r in rows[5:])
print('FINITE AND ALL-ORDER TAIL CERTIFICATES PASS')

def show(k):return [str(k[0]),str(k[1])]
Path(__file__).with_name('exponential-terms.json').write_text(json.dumps({'U':[{'lambda':show(k),'coefficient':show(v)} for k,v in U.items()],'V':[{'lambda':show(k),'coefficient':show(v)} for k,v in V.items()],'convention':'Each pair is a+b sqrt17; expression is sum coefficient * exp(lambda*t)','all_tail_bounds':'PASS'},indent=2))
