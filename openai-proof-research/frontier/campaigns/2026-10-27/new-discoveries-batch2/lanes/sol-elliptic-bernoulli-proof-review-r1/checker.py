"""Independent Laurent principal-part subtraction, no moment recurrence or IBP.
Exact sparse Q[g2,g3] throughout. Finite diagnostics, not an all-order proof.
"""
import resource,signal,json,math
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(40,40));signal.alarm(50)
from fractions import Fraction as F
from pathlib import Path
def add(*ps):
 r={}
 for p in ps:
  for k,v in p.items():r[k]=r.get(k,F(0))+v
 return {k:v for k,v in r.items() if v}
def scale(p,s):return {k:v*s for k,v in p.items() if v*s}
def mul(p,q):
 r={}
 for (a,b),v in p.items():
  for (c,d),w in q.items():r[(a+c,b+d)]=r.get((a+c,b+d),F(0))+v*w
 return {k:v for k,v in r.items() if v}
def delta(p):
 r={}
 for (a,b),v in p.items():
  if a:r=add(r,{(a-1,b+1):6*a*v})
  if b:r=add(r,{(a+2,b-1):F(b,3)*v})
 return r
N=16
c={2:{(1,0):F(1,20)},3:{(0,1):F(1,28)}}
for n in range(4,N+2):
 c[n]=scale(add(*(mul(c[j],c[n-j]) for j in range(2,n-1))),F(3,(2*n+1)*(n-3)))
p={-2:{(0,0):F(1)},**{2*n-2:v for n,v in c.items()}}
rows=[]
for m in range(1,N+1):
 d=m-1
 def df(e):
  return math.prod(range(e-d+1,e+1)) if d else 1
 ds={e-d:scale(v,df(e)) for e,v in p.items() if df(e)}
 sq={}
 for e,v in ds.items():
  for f,w in ds.items():
   if e+f<=0:sq[e+f]=add(sq.get(e+f,{}),mul(v,w))
 # wp^(2k) has just one negative Laurent term (2k+1)! z^(-2k-2).
 # Subtract those exact derivatives; remaining elliptic function is a*wp+b.
 a=sq.get(-2,{})
 b=sq.get(0,{})
 for e,v in sq.items():
  if e<-2:
   assert e%2==0
   k=(-e-2)//2
   b=add(b,scale(mul(v,c[k+1]),-F(1,2*k+1)))
 if m==1:targetA={(1,0):F(1,12)};targetB={}
 else:
  targetA=scale(delta(c[m]),math.factorial(2*m-2))
  targetB=scale(c[m],2*m*math.factorial(2*m-2))
 assert b==scale(targetA,(-1)**(m-1)),('omega',m)
 assert a==scale(targetB,(-1)**(m-1)),('eta',m)
 if m>=2:
  for q,weight in [(c[m],m),(delta(c[m]),m+1)]:
   assert all(v>0 for v in q.values())
   assert set(q)=={(a,b) for a in range(weight//2+1) for b in range(weight//3+1) if 2*a+3*b==weight}
 rows.append({'m':m,'pass':True,'omega_terms':len(b),'eta_terms':len(a)})
Path(__file__).with_name('checker-evidence.json').write_text(json.dumps({'route':'literal differentiated Laurent square; subtract single-principal-part exact even derivatives of wp; read constant and wp residual','orders':rows,'pass':True,'limits':'512MiB AS,40CPU,50alarm; external55wall; BLAS1','proof':False},indent=2))
print('PASS:16 literal Laurent/de Rham reductions;30 full-support checks')
