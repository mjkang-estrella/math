"""Finite floating diagnostics, not a proof or acceptance gate. Outputs only own root."""
from pathlib import Path
from collections import Counter,defaultdict
from fractions import Fraction
import math,json
ROOT=Path(__file__).resolve().parents[1]
def entropy(vals):return -sum(x*math.log(x) for x in vals if x)
def counts(F):return Counter(a|b for a in F for b in F)
def analyze(F,theta=1):
 N=len(F);r=counts(F);c=[[math.log(r[a|b]) for b in F] for a in F]
 means=[sum(row)/N for row in c];mean=sum(means)/N
 R=[[c[i][j]-means[i]-means[j]+mean for j in range(N)] for i in range(N)]
 K=[[math.exp(-theta*x) for x in row] for row in c]
 u=[1.0]*N;v=[1.0]*N
 for it in range(10000):
  u=[1/(N*sum(K[i][j]*v[j] for j in range(N))) for i in range(N)]
  v=[1/(N*sum(K[i][j]*u[i] for i in range(N))) for j in range(N)]
  if it%10==0:
   err=max(abs(u[i]*sum(K[i][j]*v[j] for j in range(N))-1/N) for i in range(N))
   if err<1e-13:break
 else:raise RuntimeError('nonconvergence')
 nu=defaultdict(float)
 for i,a in enumerate(F):
  for j,b in enumerate(F):nu[a|b]+=u[i]*K[i][j]*v[j]
 H0=entropy([x/N**2 for x in r.values()]);gain=entropy(nu.values())-H0
 return {'N':N,'theta':theta,'gain':gain,'V':sum(x*x for row in R for x in row)/N**2,'deficit':math.log(N)-H0,'marginal_error':err}
def prefix(F,mask):
 N=len(F);groups=defaultdict(list)
 for a in F:groups[a&mask].append(a)
 nu=defaultdict(Fraction)
 for group in groups.values():
  for a in group:
   for b in group:nu[a|b]+=Fraction(1,N*len(group))
 return nu
report={'method':'binary64 arithmetic unless rational probabilities explicitly serialized; no universal inference','prefix':{},'products':[],'chains':[]}
worst=(0,None);count=0
for familymask in range(1,1<<16):
 F=[a for a in range(16) if familymask>>a&1]
 if len(F)<2 or any(not(familymask>>(a|b)&1) for a in F for b in F):continue
 count+=1;N=len(F);r=counts(F);H0=entropy([x/N**2 for x in r.values()])
 for mask in range(1,15):
  nu=prefix(F,mask);d=entropy([float(x) for x in nu.values()])-H0
  if d<worst[0]-1e-13:worst=(d,{'family':F,'mask':mask,'iid':{str(s):str(Fraction(v,N*N)) for s,v in r.items()},'prefix':{str(s):str(v) for s,v in nu.items()}})
report['prefix']={'families_checked_n4':count,'minimum_gain':worst[0],'witness':worst[1]}
for d in range(1,7):report['products'].append({'d':d,**analyze(list(range(1<<d)))})
for N in [2,4,8,16,32,64]:report['chains'].append(analyze([(1<<k)-1 for k in range(N)]))
(ROOT/'private/coupling-diagnostics.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
