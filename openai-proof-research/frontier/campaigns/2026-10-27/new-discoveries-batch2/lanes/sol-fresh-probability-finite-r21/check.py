"""Exact diagnostics; not a conjecture proof. Run: timeout 50 python check.py."""
import resource, os, json, math, itertools, time
from pathlib import Path
from fractions import Fraction as Q
from functools import lru_cache
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(40,40))
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
b=Path(__file__).resolve().parent
start=time.monotonic()
def trim(a):
 a=list(a)
 while len(a)>1 and not a[-1]:a.pop()
 return tuple(a)
def add(a,c):
 z=[Q(0)]*max(len(a),len(c))
 for i,x in enumerate(a):z[i]+=x
 for i,x in enumerate(c):z[i]+=x
 return trim(z)
def scale(a,c):return trim([x*c for x in a])
def mul(a,c):
 z=[Q(0)]*(len(a)+len(c)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(c):z[i+j]+=x*y
 return trim(z)
def shift(a,k):return (Q(0),)*k+tuple(a)
def div1minus(a,k):
 for _ in range(k):
  out=[];v=Q(0)
  for x in a:v+=x;out.append(v)
  assert out[-1]==0
  a=trim(out[:-1])
 return a
@lru_cache(None)
def parts(n,m=None):
 if n==0:return ((),)
 m=n if m is None else min(m,n)
 return tuple((a,)+c for a in range(m,0,-1) for c in parts(n-a,a))
@lru_cache(None)
def power(n):
 # Newton identities, e_j = q^(j choose 2)/j!.
 z=shift((Q((-1)**(n-1)*n,math.factorial(n)),),n*(n-1)//2)
 for j in range(1,n):
  z=add(z,scale(shift(power(n-j),j*(j-1)//2),Q((-1)**(j-1),math.factorial(j))))
 return z
@lru_cache(None)
def aug(lam):
 if len(lam)==1:return power(lam[0])
 a=lam[-1];mu=lam[:-1];z=mul(power(a),aug(mu))
 for i in range(len(mu)):
  c=list(mu);c[i]+=a;z=add(z,scale(aug(tuple(sorted(c,reverse=True))),-1))
 return z
@lru_cache(None)
def row(n):return scale(div1minus(power(n),n-1),math.factorial(n-1))
def setparts(n):
 if n==0:yield ();return
 for pi in setparts(n-1):
  yield pi+((n-1,),)
  for i in range(len(pi)):yield pi[:i]+(pi[i]+(n-1,),)+pi[i+1:]
def mobiusF(lam):
 z=(Q(0),)
 for pi in setparts(len(lam)):
  term=(Q(1),)
  for block in pi:
   w=sum(lam[i] for i in block)
   term=mul(term,scale(row(w),Q(math.factorial(len(block)-1),math.factorial(w-1))))
  for _ in range(len(lam)-len(pi)):term=mul(term,(-1,1))
  z=add(z,term)
 return scale(z,math.factorial(sum(lam)-1))
def nu(lam):return sum(i*a for i,a in enumerate(lam))
def normalized(lam):
 f=scale(div1minus(aug(lam),sum(lam)-len(lam)),math.factorial(sum(lam)-1))
 v=nu(lam);assert all(x==0 for x in f[:v]);return trim(f[v:]),f
checks=0
for n in range(1,9):
 for lam in parts(n):
  j,f=normalized(lam);assert f==mobiusF(lam)
  d=(n-1)*(n-2)//2+len(lam)-1-nu(lam)
  assert len(j)==d+1 and all(x.denominator==1 and x>0 for x in j)
  checks+=1
j321,_=normalized((3,2,1));assert j321==(10,30,35,35,30,20,12,6,2)
# Proposed coefficientwise domination fails: A F_(2) F_(1) - F_(3) = -q.
dominance=add(scale(mul(row(2),row(1)),2),scale(row(3),-1));assert dominance==(0,-1)
# Cubic q^3+3q^2+6q+6 has nonreal roots, discriminant -216.
a,c,d,e=1,3,6,6
disc=c*c*d*d-4*a*d**3-4*c**3*e-27*a*a*e*e+18*a*c*d*e
assert row(4)==(6,6,3,1) and disc==-216
out={'status':'PASS','all_partition_sizes':[1,8],'partition_comparisons':checks,'J321':list(map(int,j321)),'dominance_counterexample':{'lambda':[2,1],'difference':[0,-1]},'row4_discriminant':disc,'wall_seconds':time.monotonic()-start,'caps':{'AS_MiB':512,'CPU_seconds':40,'external_wall_seconds':50,'BLAS_threads':1},'scope':'Finite evidence plus route counterexamples only. No all-partition proof.'}
(b/'checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
