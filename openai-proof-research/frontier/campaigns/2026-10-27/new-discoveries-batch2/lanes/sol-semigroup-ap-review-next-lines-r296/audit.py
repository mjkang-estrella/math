"""Independent AP partition and Boolean-DP witness audit; no author imports."""
from fractions import Fraction as Q
from itertools import combinations
from math import gcd
from pathlib import Path
import json
L=Path(__file__).resolve().parent
# On the AP line collapse each generator monomial to degree*d + index*t.
# All degree <=12 representations, including zero only for cutoff events.
forms={(d,j) for d in range(13) for j in range(2*d+1)}
events={Q(0),Q(1,2)}
for (d,j),(e,k) in combinations(forms,2):
 if j!=k:
  x=Q(e-d,j-k)
  if 0<=x<=Q(1,2):events.add(x)
events=sorted(events)
# All three a residues and both nonzero t residues; a and t may coincide.
def good(x):
 groups={}
 for d,j in forms:
  if d and d+j*x<=12:groups.setdefault(d+j*x,[]).append((d,j))
 out=[]
 for ar in range(3):
  for tr in (1,2):
   seq=[]
   for _,fs in sorted(groups.items()):
    rs={(d*ar+j*tr)%3 for d,j in fs}
    if len(rs)!=1:break
    seq.append(next(iter(rs)))
   else:
    if all(len(set(seq[i:i+3]))==3 for i in range(0,len(seq)-2,3)):out.append([ar,tr])
 return out
segments=[dict(lo=str(l),hi=str(r),residues=rs) for l,r in zip(events,events[1:]) if (rs:=good((l+r)/2))]
vertices=[dict(t_over_a=str(x),residues=rs) for x in events[1:-1] if (rs:=good(x))]
assert all(Q(s['hi'])<=Q(1,9) for s in segments)
exceptions=[Q(v['t_over_a']) for v in vertices if Q(v['t_over_a'])>Q(1,9)]
assert exceptions==list(map(Q,['1/8','2/13','1/5','1/4','2/7','1/3','2/5']))
assert [(x.denominator,x.numerator) for x in exceptions if x.denominator>=12]==[(13,2)]
def dp(a,t):
 A=[0]*a
 for j in range(a):A[j*t%a]=((j+1)//2)*a+j*t
 F=max(A)-a
 reachable=[True]+[False]*(F+a+8)
 for n in range(1,len(reachable)):
  reachable[n]=any(n>=g and reachable[n-g] for g in (a,a+t,a+2*t))
 assert all(v==(n>=A[n%a]) for n,v in enumerate(reachable))
 seq=[n for n in range(1,len(reachable)) if reachable[n]]
 failed=[(i+1,seq[i:i+3]) for i in range(0,len(seq)-2,3) if len({z%3 for z in seq[i:i+3]})<3]
 source=(t==1 and a%3==2) or (t==2 and a%6==1)
 assert bool(failed)!=source
 if not source:
  windows=[(1,12*a),(F-a-2*t-4,F+4)]
  i=(a+2*t-1)//(2*t)+4;B=F-(i+1)*a
  windows.append((B-6*t,B))
  assert any(lo<=tri[0]<=tri[-1]<=hi for _,tri in failed for lo,hi in windows)
 if a>9*t and a%2 and a%3==2 and t%3==1 and t>=4:
  assert B-6*t>0 and 2*i+3<a
  holes={n for n in range(B-6*t,B+1) if not reachable[n]}
  predicted={F-r*a-j*t for r in (i,i+1) for j in range(2*r+2) if B-6*t<=F-r*a-j*t<=B}
  assert holes==predicted
 return dict(a=a,t=t,source=source,witness=None if source else failed[0])
pairs=[(a,t) for a in range(12,110) for t in range(1,(a+1)//2) if 2*t<a and gcd(a,t)==1]
pairs += [(a,t) for a,t in [(101,4),(137,7),(299,10),(401,13),(1001,4),(1001,10),(128,7),(13,2)] if gcd(a,t)==1]
rows=[dp(a,t) for a,t in pairs]
result=dict(events=len(events),segments=segments,vertices=vertices,DP_pairs=len(rows),targeted=rows[-8:])
(L/'audit-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
