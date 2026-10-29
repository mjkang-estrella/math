import json,hashlib,itertools,math,sys
from fractions import Fraction as F
from pathlib import Path
L=Path(__file__).resolve().parent
def mul(a,b):
 c=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
def interpolate(xs,ys):
 ans=[F(0)]*len(xs)
 for i,x in enumerate(xs):
  p=[F(1)];den=1
  for j,z in enumerate(xs):
   if j!=i:p=mul(p,[-z,1]);den*=x-z
  for j,v in enumerate(p):ans[j]+=v*F(ys[i],den)
 return ans
def period_check(a):
 # Exact DP followed by exact rational interpolation on each N-residue.
 # Universal degree <=len(a)-1 and period N are classical/source inputs.
 N=math.lcm(*a);n=len(a);bound=N*(n+2)-1
 q=[0]*(bound+1);q[0]=1
 for w in a:
  for k in range(w,bound+1):q[k]+=q[k-w]
 polys=[]
 for r in range(N):
  xs=[r+N*t for t in range(n)];p=interpolate(xs,[q[x] for x in xs]);polys.append(p)
  for t in (n,n+1):
   x=r+N*t;assert sum(v*x**j for j,v in enumerate(p))==q[x]
 periods=[]
 for j in range(n):
  periods.append(next(d for d in range(1,N+1) if N%d==0 and all(polys[r][j]==polys[(r+d)%N][j] for r in range(N))))
 return periods
out={}
a=(1,1,2,2,2,2,13);p=period_check(a);assert p[0]==13;out['public_witness']={'weights':a,'coefficient_periods':p,'predicted_c0':26,'extra_values_per_residue':2}
# Explicit bounded exploration of the source's relaxed-Theorem2 question.
count=0;fail=[]
for n in range(2,6):
 for a in itertools.combinations_with_replacement(range(1,13),n):
  if not all(a[i+1]%a[i]==0 for i in range(n-1)):continue
  count+=1;p=period_check(a);expected=list(reversed(a))
  if p!=expected:fail.append({'a':a,'actual':p,'expected':expected})
out['relaxed_chains']={'lengths':[2,5],'max_weight':12,'cases':count,'failures':fail,'proof':False}
assert not fail
# Initial hyperbolic cancellation formula checked by direct low-order formal
# exponential multiplication, independent of quasipolynomial interpolation.
lam=F(23,2);alpha=F(2,3)+F(2,8)+F(169,8)
assert lam**3/6-alpha*lam==0
out['public_cancellation']=str(lam**3/6-alpha*lam)
out['failed_strict_pole_route']={'weights':[1,2,2],'j':0,'primitive_root':-1,'actual_pole_order':2,'strict_proof_required_order':1,'coefficient_periods':period_check((1,2,2))}
assert out['failed_strict_pole_route']['coefficient_periods']==[2,2,1]
if (L/'source-lock.json').exists():
 lock=json.loads((L/'source-lock.json').read_text())
 for p,h in lock.items():assert hashlib.sha256((L/p).read_bytes()).hexdigest()==h,p
 out['source_hashes_verified']=len(lock)
(L/'check-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
