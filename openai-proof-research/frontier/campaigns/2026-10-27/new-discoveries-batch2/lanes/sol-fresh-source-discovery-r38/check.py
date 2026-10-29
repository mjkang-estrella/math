import os,resource,signal,json,math
from pathlib import Path
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']: os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(35,35));signal.alarm(45)
import sympy as s
from fractions import Fraction as F
b=Path(__file__).parent
B=lambda n:1 if n==0 else sum(2*math.comb(n+1,k-1)*math.comb(n+1,k)*math.comb(n+1,k+1) for k in range(1,n+1))//(n*(n+1)**2)
v=[B(n) for n in range(65)]
for n in range(1,63):assert (n+4)*(n+5)*v[n+2]==(7*n*n+35*n+40)*v[n+1]+8*n*(n+1)*v[n]
# Independent generation by the published recurrence.
w=[1,2]
for n in range(1,63):
 num=(7*n*n+35*n+40)*w[-1]+8*n*(n+1)*w[-2];den=(n+4)*(n+5)
 assert num%den==0;w.append(num//den)
assert w==v[1:]
h0=int(s.det(s.Matrix(5,5,lambda i,j:v[i+j])))
h2=int(s.det(s.Matrix(6,6,lambda i,j:v[i+j+2])))
assert h0==-616 and h2==-115894592
# Positivity is not propagated by the source recurrence plus first-order positivity.
t=s.symbols('t');a=[s.Integer(1),t]
for n in range(1,4):a.append(s.expand(((7*n*n+35*n+40)*a[-1]+8*n*(n+1)*a[-2])/((n+4)*(n+5))))
l=[s.expand(a[i]*a[i+2]-a[i+1]**2) for i in range(3)]
p2=s.factor(l[0]*l[2]-l[1]**2);x=s.Rational(117,50)
assert all(z.subs(t,x)>0 for z in l) and p2.subs(t,x)<0
# Ambrus: classical same-source bounds already yield all p>=4.
p,u=s.symbols('p u');L=lambda p:2*p*p/(2*p*p+p-1);U=lambda p:p*(2*p+1)**2/(2*(p+1)**2*(2*p-1))
ratio=s.factor(L(p+1)/U(p)-1)
assert s.factor(ratio-(2*p**3-5*p**2-10*p-4)/(p*(p+2)*(2*p+1)**3))==0
assert s.expand((2*p**3-5*p**2-10*p-4).subs(p,u+4))==2*u**3+19*u**2+46*u+4
# Eulerian central values independently by recurrence and Eq4.2 alternating sum.
row=[1];fs={}
for m in range(1,11):
 old=row;row=[(k+1)*(old[k] if k<len(old) else 0)+(m-k)*(old[k-1] if k else 0) for k in range(m)]
 lidx=m//2+1
 alt=sum((-1)**i*math.comb(m+1,i)*(lidx-i)**m for i in range(lidx+1))
 assert alt==max(row);fs[m]=F(alt,math.factorial(m))
assert fs[4]==F(11,24) and fs[6]==F(151,360) and fs[8]==F(15619,40320)
gap=fs[4]*fs[8]-fs[6]**2
assert gap==F(23423,14515200)>0
out=dict(status='PASS',baxter_recurrence_terms=64,hankel_B0_5=h0,hankel_B2_6=h2,recurrence_obstruction_ratio=str(x),recurrence_obstruction_L2=str(p2.subs(t,x)),L2_polynomial=str(p2),classical_ratio=str(ratio),ambrus_p3_gap=str(gap),ambrus_actual_values={str(m):str(fs[m]) for m in [4,6,8]},limit='Exact finite checks, not Baxter conjecture proof')
(b/'checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
