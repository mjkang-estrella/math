import pathlib,itertools,json,math,sys
import numpy as np
from scipy.optimize import milp,LinearConstraint,Bounds
from fractions import Fraction
D=pathlib.Path(__file__).resolve().parents[1]
def parts(n,cap=None):
 if n==0:return [()]
 return [(a,)+p for a in range(min(n,cap if cap is not None else n),0,-1) for p in parts(n-a,a)]
def bps(n):return [(a,b) for k in range(n+1) for a in parts(k) for b in parts(n-k)]
def rem(p):return [p[:i]+((a-1,) if a>1 else ())+p[i+1:] for i,a in enumerate(p) if i==len(p)-1 or a>p[i+1]]
def dim(p,k):
 if len(p)>k:return 0
 ans=Fraction(1)
 for i,a in enumerate(p):
  for j in range(a):ans*=Fraction(k+j-i,a-j+sum(v>j for v in p[i+1:]))
 assert ans.denominator==1
 return ans.numerator
start=int(sys.argv[1]);end=int(sys.argv[2]);out=[]
for n in range(start,end+1):
 rows=bps(n);cols=bps(n+1);ix={p:i for i,p in enumerate(rows)};R=np.zeros((len(rows),len(cols)))
 for j,(a,b) in enumerate(cols):
  for aa in rem(a):R[ix[aa,b],j]=1
  for bb in rem(b):R[ix[a,bb],j]=1
 for m in range(1,16):
  plus=(m+math.gcd(2,m))//2;minus=(m-math.gcd(2,m))//2
  target=[dim(a,plus)*dim(b,minus) for a,b in rows]
  if max(target)>2**50:continue
  ans=milp(np.zeros(len(cols)),integrality=np.ones(len(cols)),bounds=Bounds(0,np.inf),constraints=LinearConstraint(R,target,target),options={'time_limit':4,'threads':1})
  cert=None
  if ans.x is not None:
   v=[int(round(x)) for x in ans.x]
   if all(sum(int(R[i,j])*v[j] for j in range(len(v)))==target[i] for i in range(len(target))) and min(v)>=0:cert=[(cols[j],v[j]) for j in range(len(v)) if v[j]]
  r=dict(n=n,m=m,status=int(ans.status),message=ans.message,verified_integer_certificate=cert)
  out.append(r);print(n,m,ans.status,cert is not None,flush=True)
 (D/f'outputs/parking-{n}.json').write_text(json.dumps([r for r in out if r['n']==n],indent=2)+'\n')
