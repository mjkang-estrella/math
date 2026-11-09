from pathlib import Path
from functools import lru_cache
from fractions import Fraction as F
import json,itertools
L=Path(__file__).parent

def moves(s):
 out=[];n=len(s)
 def put(name,changes):
  t=list(s)
  for i,v in changes:t[i]+=v
  assert min(t)>=0
  out.append((name,tuple(t)))
 if s[0]>=2:put('C1',[(0,-2),(1,1)])
 for i in range(1,n-1):
  if s[i-1] and s[i]:put('C'+str(i+1),[(i-1,-1),(i,-1),(i+1,1)])
  if s[i]>=2:put('S'+str(i+1),[(i,-2),(0 if i==1 else i-2,1),(i+1,1)])
 return out
states=set();hazards=0;root_paths=0
for N in range(2,15):
 fib=[1,2]
 while fib[-1]<=N:fib.append(sum(fib[-2:]))
 n=len(fib)-1;dim=len(fib)+1
 @lru_cache(None)
 def visit(s):
  global hazards
  states.add(s);ms=moves(s)
  assert all(sum(a*b for a,b in zip(s,fib+[sum(fib[-2:])]))==sum(a*b for a,b in zip(t,fib+[sum(fib[-2:])] )) for _,t in ms)
  if sum(s)>n+2:
   if any(a.startswith('S') for a,_ in ms):hazards+=1
   else:
    cur=s
    for a in ['C1','C1','S2']:
     choices=dict(moves(cur));assert a in choices;cur=choices[a]
    hazards+=1
  for _,t in ms:visit(t)
 visit(tuple([N]+[0]*(dim-1)))
 # Exhaustive complete paths only N<=10, to check strict stopping-event indices.
 if N<=10:
  def walk(s,x):
   global root_paths
   ms=moves(s)
   if not ms:
    T=len(x);C=T-sum(x);root_paths+=1
    for m in range(1,T+4):assert (T<m)==(m-sum(x[:m])>C)
    return
   for a,t in ms:walk(t,x+[int(a.startswith('S'))])
  walk(tuple([N]+[0]*(dim-1)),[])
# Analytic scales evaluated as logarithms, not finite length histograms.
import math
scales=[]
for n in [100,500,1000,10000]:
 # c=3/2; V>=c^n/(6n); Q(3n^6) <= (3n^6+2)*sqrt(pi/(8V))
 logQ=math.log(3*n**6+2)+.5*(math.log(math.pi/8)+math.log(6*n)-n*math.log(1.5))
 logSuffix=math.log(3)+ (n+1)*math.log(2)-n*n/8
 scales.append(dict(n=n,log_anti_concentration_upper=logQ,log_suffix_failure_upper=logSuffix,b_le_k=(3*n**5+n+3<=n**6)))
result=dict(status='PASS',reachable_states=len(states),high_token_hazard_checks=hazards,complete_paths_identity_checks=root_paths,scales=scales,scope='Local hazard and root event checks only; no asymptotic proof by numerics',limits=dict(AS=536870912,groupRSS=536870912,CPU=210,wall=230,raises=False))
(L/'diagnostics.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
