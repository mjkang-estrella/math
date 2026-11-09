from pathlib import Path
from fractions import Fraction as Q
from itertools import combinations
from math import gcd
import json
L=Path(__file__).resolve().parent
out=[]
for typ in (0,1):
 forms={(i+(j if typ else 0),2*j+3*k if not typ else j+3*k) for i in range(13) for j in range(13-i) for k in range(13-i-j)}
 events={Q(1,2),Q(2,3)}
 for (i,j),(k,l) in combinations(forms,2):
  if j!=l:
   x=Q(k-i,j-l)
   if Q(1,2)<=x<=Q(2,3):events.add(x)
 events=sorted(events)
 def good(x):
  groups={}
  for i,j in forms:
   if 0<i+j*x<=12:groups.setdefault(i+j*x,[]).append((i,j))
  good=[]
  for ar in range(3):
   for tr in range(3):
    seq=[]
    for _,fs in sorted(groups.items()):
     rs={(i*ar+j*tr)%3 for i,j in fs}
     if len(rs)!=1:break
     seq.append(next(iter(rs)))
    else:
     if all(len(set(seq[i:i+3]))==3 for i in range(0,len(seq)-2,3)):good.append([ar,tr])
  return good
 segments=[dict(lo=str(l),hi=str(r),residues=rs) for l,r in zip(events,events[1:]) if (rs:=good((l+r)/2))]
 vertices=[dict(x=str(x),primitive=[x.denominator,x.numerator],residues=rs) for x in events[1:-1] if (rs:=good(x))]
 out.append(dict(type=typ,events=len(events),segments=segments,vertices=vertices))
(L/'next-ratio.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
