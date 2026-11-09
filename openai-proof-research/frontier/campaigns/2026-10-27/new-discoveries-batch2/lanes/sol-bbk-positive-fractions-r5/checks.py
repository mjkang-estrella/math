"""Exact bounded replay. Writes only beside this script; no solver/imported checker."""
import os
for v in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[v]='1'
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(100,100))
import json,hashlib,datetime
from pathlib import Path
from fractions import Fraction as F
P=Path(__file__).resolve().parent; OLD=P.parent/'root-bbk-positive-fractions-r1'
def mul(a,b):
 c={}
 for i,x in a.items():
  for j,y in b.items():c[i+j]=c.get(i+j,0)+x*y
 return {i:x for i,x in c.items() if x}
def prod(ds):
 a={0:F(1)}
 for d in ds:a=mul(a,{0:F(1),d:F(-1)})
 return a
def add(a,b):
 c=a.copy()
 for i,x in b.items():c[i]=c.get(i,0)+x
 return {i:x for i,x in c.items() if x}
def clear(z,ds):
 r={}
 for j,a in enumerate(z):r=add(r,mul(a,prod(ds[:j]+ds[j+1:])))
 return r
seen=set();fractional=0;hashes={}
for name in ['results.json','selected-results.json']:
 b=(OLD/name).read_bytes();hashes[name]=hashlib.sha256(b).hexdigest()
 for r in json.loads(b):
  k,n=r['k'],r['n'];assert (k,n) not in seen;seen.add((k,n))
  ds=list(range(1,2*n+2,2));D=2*n*(k-2)-1;M=n*(2*k+n-2)
  z=[{} for _ in ds]
  for t in r['nonzero']:
   j,a,x=t['j'],t['a'],F(t['coefficient']);assert x>0 and 0<=a<=D+ds[j]
   assert a not in z[j];z[j][a]=x;fractional+=x.denominator!=1
  N=prod(range(2*k-1,2*k+2*n-1,2));assert clear(z,ds)==N
  zs=[{a:x/2 for a,x in s.items()} for s in z]
  for j,s in enumerate(z):
   for a,x in s.items():zs[j][D+ds[j]-a]=zs[j].get(D+ds[j]-a,0)+x/2
  assert clear(zs,ds)==N
  # Verify finite progression system independently from numerator/denominator DP.
  b=[F(0)]*(M+1)
  for i,x in N.items():b[i]=x
  for d in ds:
   for i in range(d,M+1):b[i]+=b[i-d]
  assert all(b[i]==sum(x for j,s in enumerate(z) for a,x in s.items() if i>=a and (i-a)%ds[j]==0) for i in range(M+1))
# Exact semigroup criterion for all bounded d,e,h, via coin-count difference.
semigroup_cases=0
for d in range(1,19):
 for e in range(1,19):
  coin=[0]*181;coin[0]=1
  for a in [d,e]:
   for i in range(a,181):coin[i]+=coin[i-a]
  for h in range(1,61):
   rep=next(((u,(h-u*d)//e) for u in range(h//d+1) if (h-u*d)%e==0),None)
   if rep is None:assert coin[h]-1==-1
   else:
    u,v=rep
    lhs=prod([h]);rhs=add(mul({i*d:F(1) for i in range(u)},prod([d])),mul({u*d+i*e:F(1) for i in range(v)},prod([e])))
    # Above rhs equals (1-q^(ud))+q^(ud)(1-q^(ve)).
    assert lhs==rhs
    assert min(coin[i]-(coin[i-h] if i>=h else 0) for i in range(181))>=0
   semigroup_cases+=1
# Structural recurrence example: full rational identity by cross-multiplication.
def frac(k,n):return prod(range(2*k-1,2*k+2*n-1,2)),prod(range(1,2*n+2,2))
a,b=frac(7,4);c,dn=frac(6,4)
left=add(mul(a,dn),{i:-v for i,v in mul(c,b).items()})
rn=mul({11:F(1)},mul(prod([8]),prod([13,15,17])))
rd=prod([1,3,5,7,9])
assert mul(left,rd)==mul(rn,mul(b,dn))
prefix=[0]*9;prefix[0]=1
for weight in [1,3,5,7,9]:
 for i in range(weight,9):prefix[i]+=prefix[i-weight]
assert prefix[8]-1==5
bad=[0]*9;bad[0]=1
for weight in [7,9]:
 for i in range(weight,9):bad[i]+=bad[i-weight]
assert bad[8]-1==-1
# No exponential tree enumeration: invariant forbids all cancellation trees.
obstructions=[]
for m in range(4,101):
 d,e=2*m-3,2*m-1;hs=list(range(2*m+1,4*m-2,2))
 assert len(hs)==m-1 and 3*d>max(hs) and min(hs)>e
 for h in hs:
  assert all(h-u*d<0 or (h-u*d)%e for u in range(h//d+1))
 obstructions.append({'m':m,'protected':[d,e],'numerator_count':len(hs),'low_denominator_count':m-2})
out={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','saved_full_identities':len(seen),'reciprocal_averaged_full_identities':len(seen),'fractional_nonzero_coefficients':fractional,'saved_input_sha256':hashes,'semigroup_criterion_cases':semigroup_cases,'cancellation_tree_invariant_examples':obstructions,'full_BBK_proved':False,'credit':0}
P.joinpath('checks.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k!='cancellation_tree_invariant_examples'})
