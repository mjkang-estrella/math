import os,resource,signal,json,math,pathlib
from fractions import Fraction as F
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(20,20));signal.alarm(25)
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
p=pathlib.Path(__file__).parent
# Independent exact power-basis expansion; no candidate checker imported.
def mul(a,b):
 c=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
def power(a,n):
 c=[F(1)]
 for _ in range(n):c=mul(c,a)
 return c
def expand(bs):
 n=len(bs)-1;c=[F(0)]*(n+1)
 for k,b in enumerate(bs):
  for j,v in enumerate(power([1,-1],n-k)):c[k+j]+=b*v
 return c
def value(a,x):
 y=F(0)
 for z in a[::-1]:y=y*x+z
 return y
cases=0
for n in range(1,21):
 for t in range(7):
  bs=[(k*k+3*t)% (math.comb(n,k)+1) for k in range(n+1)]
  a=expand(bs)
  for j in range(9):
   x=F(j,8);assert value(a,x)==sum(bs[k]*x**k*(1-x)**(n-k) for k in range(n+1))
  recovered=[sum(a[j]*math.comb(n-j,k-j) for j in range(k+1)) for k in range(n+1)]
  assert recovered==bs;cases+=1
# Degree elevation preserves positivity and upper bounds, independently via Pascal.
elev=0
for n in range(1,15):
 bs=[k%(math.comb(n,k)+1) for k in range(n+1)]
 nxt=[(bs[k] if k<=n else 0)+(bs[k-1] if k else 0) for k in range(n+2)]
 assert all(0<=b<=math.comb(n+1,k) for k,b in enumerate(nxt));a=expand(bs);b=expand(nxt);assert b==a+[0];elev+=1
# Endpoint derivative sign solvability for both signs of m(0),m(1).
end=0
for m0 in [-9,-2,1,7]:
 for m1 in [-8,-1,3,9]:
  for a0 in [-12,0,14]:
   for a1 in [-15,0,11]:
    N0=next(z for z in range(-40,41) if a0+m0*z>0)
    N1=next(z for z in range(-40,41) if a1-m1*z<0)
    assert a0+m0*N0>0 and a1-m1*N1<0;end+=1
# Trace-dual discriminant calculation for x^3-3x+1, a totally real non-sPV test.
# Newton traces: T0=3,T1=0,T2=6,T3=-3,T4=18.
A=[[3,0,6],[0,6,-3],[6,-3,18]]
det=A[0][0]*(A[1][1]*A[2][2]-A[1][2]*A[2][1])+A[0][2]*(A[1][0]*A[2][1]-A[1][1]*A[2][0]);assert det==81
out={'status':'PASS bounded algebraic diagnostics only','basis_cases':cases,'rational_evaluations':cases*9,'degree_elevations':elev,'endpoint_sign_cases':end,'trace_gram_determinant':det,'universal_topology_or_approximation_proved_by_script':False,'lean_compiled':False}
(p/'checks-review.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
