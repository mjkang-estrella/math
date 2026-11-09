"""Exact diagnostics only; no all-order proof. Python3 standard library."""
import os,resource,json,math
os.environ.update({x:'1' for x in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','BLIS_NUM_THREADS']})
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(35,35))
from fractions import Fraction as F
from pathlib import Path
P=Path(__file__).resolve().parent

def deriv(a):return [i*a[i] for i in range(1,len(a))]
def mul(a,b):
 c=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b): c[i+j]+=x*y
 return c
def integ(a):return [F(0)]+[x/F(i+1) for i,x in enumerate(a)]
def ev(a,x):
 y=F(0)
 for z in reversed(a):y=y*x+z
 return y
q=[[F(0),F(1)],[F(1),F(-1)]];k=[F(1)]
for n in range(1,11):
 Q=integ(mul(deriv(q[n]),q[n-1]));kn=(-1)**n*ev(Q,F(1));k.append(kn)
 qn=[-x/kn for x in Q];qn[0]=F((n+1)%2);q.append(qn)
assert k[:7]==[F(1),F(1,2),F(1,3),F(3,10),F(2,7),F(161,572),F(24941,89148)]
d=[k[i]-k[i+1] for i in range(10)];theta={n:d[n]/d[n-1] for n in range(1,10)}
finite=[]
for m in range(1,4):
 v=[theta[2*m],theta[2*m+2],theta[2*m+3],theta[2*m+1]];assert all(v[i]<v[i+1] for i in range(3));finite.append({'m':m,'values':list(map(str,v))})
# Ordinary pointwise order fails, even for decreasing convex polynomials.
f=[F(1),F(-2),F(0),F(2),F(-1)];area=F(3,10);cross=[]
for t,s in [(F(3,5),F(4,5)),(F(4,5),F(3,5))]:
 assert t*t+s*s==1
 x=ev(f,t);assert x==((1-t)*s)**2
 Tf=(ev(integ(f),t)-t*x)/area
 Tg=1-3*x+2*((1-t)*s)**3
 cross.append({'t':str(t),'x':str(x),'Tf_minus_Tg':str(Tf-Tg)})
assert cross[0]['Tf_minus_Tg']=='16/15625' and cross[1]['Tf_minus_Tg']=='-52/46875'
# Source-level routine consequence for excluded preliminary target.
def fcentral(m):
 n=m+1
 # J_n(0) for odd m; f(even m) via source (4.10)
 if m%2==0:return F(m+1,m+2)*fcentral(m+1)
 return F(sum((-1)**j*math.comb(n,j)*(n-2*j)**(n-1) for j in range(n//2+1)),2**(n-1)*math.factorial(n-1))
small=[]
for p in [3]:
 r=fcentral(2*p+2)*fcentral(2*p-2)/fcentral(2*p)**2;assert r>1;small.append({'p':p,'ratio':str(r)})
# Tail numerator p^3-3p^2-3p-1 positive at p>=4:
# at p=q+4 equals q^3+9q^2+21q+3.
# numerator for L(p+1)/U(p)-1 verified polynomial using bounded identities,
# with hand expansion separately documented in discovery.md.
for p in range(4,21):
 L=F(2*(p+1)**2,2*(p+1)**2+p)
 U=F(p*(2*p+1)**2,2*(p+1)**2*(2*p-1))
 assert L/U>1
 assert L/U-1==F(2*(p**3-3*p*p-3*p-1),p*(2*p+1)**3*(p+2))
result={'status':'PASS','scope':'finite exact checks and route obstructions only','kappa':list(map(str,k)),'finite_source_checks':finite,'order_counterexample':cross,'excluded_sinc_small_cases':small,'positive_moment_obstruction':{'theta1':str(theta[1]),'theta2':str(theta[2])},'limits':{'address_space_bytes':512*1024**2,'cpu_seconds':35,'blas_threads':1}}
(P/'checks.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
