import resource,signal,json,hashlib,math
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(25,25));signal.alarm(40)
b=Path(__file__).resolve().parent
# Independent polynomial ring, variables p,a,r. No candidate imports or execution.
def c(n): return {(0,0,0):n} if n else {}
def add(*xs):
 d={}
 for x in xs:
  for k,v in x.items():d[k]=d.get(k,0)+v
 return {k:v for k,v in d.items() if v}
def mul(x,y):
 d={}
 for k,v in x.items():
  for l,w in y.items():
   t=tuple(a+b for a,b in zip(k,l));d[t]=d.get(t,0)+v*w
 return {k:v for k,v in d.items() if v}
def scale(n,x):return mul(c(n),x)
def sub(x,y):return add(x,scale(-1,y))
p={(1,0,0):1};a={(0,1,0):1};r={(0,0,1):1};d=sub(p,a)
lhs=sub(mul(scale(2,a),mul(p,sub(p,r))),mul(sub(a,r),sub(scale(3,mul(p,p)),scale(2,mul(a,r)))))
rhs=add(mul(sub(scale(3,r),a),mul(d,d)),mul(scale(2,a),mul(sub(scale(2,r),a),d)),mul(a,mul(sub(a,r),sub(scale(2,r),a))))
assert lhs==rhs
# Trial division only; floor division supplies strict rational next prime without floating arithmetic.
def prime(n):return n>=2 and all(n%t for t in range(2,math.isqrt(n)+1))
def nextp(n):
 n+=1
 while not prime(n):n+=1
 return n
def sr(n,r):
 v=1;t=2
 while t*t<=n:
  if n%t==0:
   e=0
   while n%t==0:n//=t;e+=1
   v*=0 if t<=r else t**(e-1)*(t-r)
  t+=1
 if n>1:v*=0 if n<=r else n-r
 return v
rows=[];count=0;equal=[];bertrand_fail=[]
for r0 in range(1,101):
 a0=nextp(r0)
 assert r0<a0<=2*r0
 for p0 in range(r0+1,501):
  if not prime(p0):continue
  q=nextp(p0*p0//a0);m=a0*q
  assert q>p0>=a0 and m>p0*p0
  assert sr(m,r0)==(a0-r0)*(q-r0)>0
  assert sr(m,r0)<=sr(p0*p0,r0)==p0*(p0-r0)
  count+=1
  if p0*p0<11*a0:rows.append([r0,p0,a0,q,m,sr(m,r0),sr(p0*p0,r0)])
  if sr(m,r0)==sr(p0*p0,r0):equal.append([r0,p0])
  # Limit of directly substituting Bertrand q <= 2x, not failure of actual witness.
  if a0*p0*(p0-r0)<(a0-r0)*(2*p0*p0-a0*r0):
   if len(bertrand_fail)<5:bertrand_fail.append([r0,p0,a0])
assert len(rows)==10 and equal==[[1,2],[2,3]]
# Actual source finite base checked with independent sieve through 400000.
N=400000;s=bytearray(b'\1')*(N+1);s[:2]=b'\0\0'
for i in range(2,math.isqrt(N)+1):
 if s[i]:s[i*i:N+1:i]=b'\0'*(((N-i*i)//i)+1)
ps=[i for i in range(N+1) if s[i]];bad=[];pairs=0
for j,(u,v) in enumerate(zip(ps,ps[1:]),1):
 if u>396738:break
 pairs+=1
 if 5*v>7*u:bad.append([j,u,v])
assert [t[0] for t in bad]==[1,2,4]
out=dict(status='PASS',identity_coefficientwise=lhs==rhs,exception_rows=rows,equality_rows=equal,finite_witness_cases=count,finite_prime_gap_pairs=pairs,prime_gap_exceptions=bad,bertrand_only_bound_failure_examples=bertrand_fail,scope='Finite arithmetic/identity checks only; infinite argument is in review.md; source Lemma2 accepted as published ordinary theorem')
(b/'own-checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
