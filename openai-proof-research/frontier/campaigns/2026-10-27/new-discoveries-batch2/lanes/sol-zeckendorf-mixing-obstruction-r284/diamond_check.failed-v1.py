from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
import json
# Load only the move generator; do not execute the other diagnostic.
scope={};text=(Path(__file__).parent/'diagnostics.py').read_text();exec(text[:text.index('states=set()')],scope);moves=scope['moves']
def canon(w):
 w=list(w)
 while True:
  for i in range(len(w)-1):
   if w[i][0]=='S':
    k=int(w[i][1:])
    if w[i+1]=='C'+str(k-1) and (i==0 or w[i-1]!='S'+str(k+1)):
     w[i:i+2]=['C'+str(k)];break
  else:return tuple(w)
rows=[]
for N in range(2,11):
 fib=[1,2]
 while fib[-1]<=N:fib.append(sum(fib[-2:]))
 start=tuple([N]+[0]*(len(fib)))
 groups=defaultdict(dict)
 def walk(s,w,p):
  ms=moves(s)
  if not ms:groups[canon(w)][tuple(w)]=p;return
  for a,t in ms:walk(t,w+[a],p/len(ms))
 walk(start,[],F(1))
 slots=0
 for r,paths in groups.items():
  s=start;eligible={}
  for i,a in enumerate(r):
   if a.startswith('C') and a!='C1':
    k=int(a[1:])
    if s[k-1]>=2 and (i==0 or r[i-1]!='S'+str(k+1)):
     mid=dict(moves(s))['S'+str(k)];eligible[i]=F(1,1+len(moves(mid)))
   s=dict(moves(s))[a]
  assert len(paths)==2**len(eligible),(N,r,len(paths),eligible)
  mass=sum(paths.values());slots+=len(eligible)
  for w,p in paths.items():
   j=0;prod=F(1)
   for i,a in enumerate(r):
    if i in eligible:
     k=int(a[1:]);expanded=w[j:j+2]==('S'+str(k),'C'+str(k-1));prod*=eligible[i] if expanded else 1-eligible[i];j+=2 if expanded else 1
    else:assert w[j]==a;j+=1
   assert j==len(w)
   assert p/mass==prod,(N,r,w,p/mass,prod)
 rows.append(dict(N=N,cells=len(groups),paths=sum(len(v) for v in groups.values()),eligible_slots=slots))
result=dict(status='PASS',scope='Exact primary one-prefix partition coverage and P_N factorization, N=2..10; no asymptotic inference',rows=rows)
(Path(__file__).parent/'diamond-check.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
