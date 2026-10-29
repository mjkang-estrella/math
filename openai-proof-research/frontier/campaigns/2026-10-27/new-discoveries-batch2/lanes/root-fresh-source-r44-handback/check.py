import resource,signal,json,math,time,pathlib
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(225)
from fractions import Fraction as Q
from functools import lru_cache
P=pathlib.Path(__file__).resolve().parent
def bc(a,k):
 if k<0:return Q(0)
 z=Q(1)
 for j in range(k):z=z*(a-j)/(j+1)
 return z
def det(a):
 a=[list(map(Q,r)) for r in a];z=Q(1)
 for i in range(len(a)):
  k=next((k for k in range(i,len(a)) if a[k][i]),None)
  if k is None:return Q(0)
  if k!=i:a[i],a[k]=a[k],a[i];z=-z
  d=a[i][i];z*=d
  for k in range(i+1,len(a)):
   f=a[k][i]/d
   for j in range(i+1,len(a)):a[k][j]-=f*a[i][j]
 return z

def mat(n,x,shift=3):return [[4**i*bc(x+i+2*j+shift,2*j+shift)+bc(x-i+2*j+shift,2*j+shift) for j in range(n)] for i in range(n)]
def coeff(i,k,x):return sum((Q(math.comb(i,l)*3**(i-l))*bc(x+k-l,k-i-l) for l in range(i+1)),Q(0))
def pref(n,x):
 z=Q(2*6**(n*(n-1)//2))*(x+2)*(x+3)
 for i in range(n):
  z*=Q(math.factorial(i),math.factorial(2*i+3))
  for j in range(n-i):z*=x+3*i+1+j
 return z
@lru_cache(None)
def pol(n,x):return det(mat(n,x))/pref(n,x)
def residual(n,x):
 a=18*n*n+9*n*x+72*n-3*x*x-3*x+49
 b=135*n**4+108*n**3*x+810*n**3-54*n*n*x*x+108*n*n*x+1395*n*n-52*n*x**3-510*n*x*x-1100*n*x+120*n-9*x**4-152*x**3-855*x*x-1780*x-1020
 c=6*(n+1)*(n-x-2)*(n+x+2)*(3*n+x+3)*(3*n+x+5)*(3*n+x+7)
 return 3*pol(n+3,x)-2*a*pol(n+2,x)+b*pol(n+1,x)-c*pol(n,x)
t=time.monotonic();counts={'recurrence_evaluations':0,'row_transform_determinants':0,'minor_identities':0}
for n in range(1,9):
 for x in range(2*n+5):
  assert residual(n,Q(x))==0,(n,x)
  counts['recurrence_evaluations']+=1
for n in range(1,8):
 for x in [Q(0),Q(1,2),Q(3),Q(-1,2)]:
  for shift in [1,3]:
   assert det(mat(n,x,shift))==2*det([[coeff(i,2*j+shift,x) for j in range(n)] for i in range(n)])
   counts['row_transform_determinants']+=1
  a=mat(n+1,x,1)
  assert det([r[1:] for r in a[:-1]])==det(mat(n,x,3))
  counts['minor_identities']+=1
# Exact symbolic division: no ordinary monic three-term recurrence with constant previous-polynomial coefficient.
import sympy as s
x=s.symbols('x');p2=x*x+Q(31,3)*x+20;p3=x**4+26*x**3+229*x*x+Q(6956,9)*x+Q(2560,3)
quot,rem=s.div(p3,p2,x)
assert rem == -Q(736,27)*x-Q(800,9)
assert 26!=2*Q(31,3)
# source initial conditions independently from literal determinant
for v in range(5):
 assert pol(1,Q(v))==1
 assert pol(2,Q(v))==p2.subs(x,v)
 assert pol(3,Q(v))==p3.subs(x,v)
result={'status':'PASS','counts':counts,'n_range':'recurrence n=1..8 ONLY','remainder':str(rem),'quadratic_variable_obstruction':{'required_x3':str(2*Q(31,3)),'actual_x3':26},'seconds':time.monotonic()-t,'limits':{'AS_MiB':512,'CPU_s':210,'alarm_s':225,'outer_wall_s':230,'BLAS_threads':1},'meaning':'exact finite-order corroboration and failed-route identities; no universal proof'}
(P/'checks.json').write_text(json.dumps(result,indent=2));print(json.dumps(result))
