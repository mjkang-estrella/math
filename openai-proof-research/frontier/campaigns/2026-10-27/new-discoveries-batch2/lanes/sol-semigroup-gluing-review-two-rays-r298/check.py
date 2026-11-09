"""Independent recurrence for actual membership; no upstream checker imports."""
from pathlib import Path
from math import gcd
from fractions import Fraction
import json
L=Path(__file__).resolve().parent
TABLE=[(3,0,3,1,6,-1),(6,1,6,2,9,3),(6,1,9,2,9,3),(6,1,6,3,6,5),(6,1,12,-4,12,0),(3,1,6,-1,6,0),(3,2,3,3,3,4),(12,2,12,4,18,3),(3,2,6,1,6,3),(6,3,6,5,12,4),(6,4,6,5,9,6),(12,4,18,3,18,5),(6,5,9,6,9,7),(6,5,12,4,12,6),(12,8,12,10,18,15),(12,8,18,13,18,15)]
def actual(gs):
 a=min(gs);v=[True];run=0
 while run<a:
  n=len(v);yes=any(n>=g and v[n-g] for g in gs)
  v.append(yes);run=run+1 if yes else 0
 v += [True]*(2*a+12)
 seq=[n for n in range(1,len(v)) if v[n]]
 return v,seq
def failures(seq):
 return [{'rank':i+1,'triple':seq[i:i+3]} for i in range(0,len(seq)-2,3) if len({n%3 for n in seq[i:i+3]})<3]
def boundary(seq,h):
 r=seq.index(h-1)+1
 if r%3==0:return None
 start=r-1 if r%3==1 else r-2
 return {'rank':start+1,'triple':seq[start:start+3]}
def gluing(c,k,m,gs):
 v,seq=actual(gs);holes={1,2,5} if c==3 else {1};f=5 if c==3 else 1
 F=(k-1)*m+f*k
 assert max(n for n in range(len(v)) if not v[n])==F
 for n,yes in enumerate(v):
  j=n*pow(m,-1,k)%k;z=(n-j*m)//k
  assert yes==(z>=0 and z not in holes)
 ap=[min(n for n in range(r,len(v),c*k) if v[n]) for r in range(c*k)]
 expected=sorted(j*m+k*x for j in range(k) for x in ([0,4,8] if c==3 else [0,3]))
 assert sorted(ap)==expected
 def N(z):return 0 if z<0 else z+1-sum(h<=z for h in holes)
 # Membership above is checked at EVERY integer. Independently sample the
 # explicit rank expression at the initial and terminal twelve members.
 for idx in sorted(set(range(min(12,len(seq))))|set(range(max(0,len(seq)-12),len(seq)))):
  n=seq[idx];assert sum(N((n-j*m)//k) for j in range(k))-1==idx+1
 offsets={i*m+k*h for i in range(k) for h in range(F//k+1) if h>=0 and h not in holes and F-i*m-k*h>0}
 assert {F-o for o in offsets}=={n for n in range(1,F+1) if not v[n]}
 return v,seq,F
def intersections():
 out=[]
 for coeff in [(4,-3,0),(4,0,-3),(3,-1,-1),(3,0,-2)]:
  for H,row in enumerate(TABLE,1):
   C=sum(coeff[i]*row[2*i] for i in range(3));D=sum(coeff[i]*row[2*i+1] for i in range(3))
   root='ALL' if C==D==0 else None if C==0 else Fraction(-D,C)
   qmin=2 if H==5 else 1
   legal=isinstance(root,Fraction) and root.denominator==1 and root>=qmin
   triple=[int(row[2*i]*root+row[2*i+1]) for i in range(3)] if legal else None
   retained=bool(triple and triple[0]>=12 and triple[0]<triple[1]<triple[2]<2*triple[0] and gcd(*triple)==1)
   if coeff[0]==4:assert root!='ALL' and not retained
   out.append(dict(support=coeff,H=H,C=C,D=D,root=str(root),legal=legal,triple=triple,retained=retained))
 return out
counts={'4a=3b':0,'4a=3d':0,'3a=2d':0,'3a=b+d':0};examples={}
for k in range(4,41):
 for typ in [0,1]:
  label=['4a=3b','4a=3d'][typ]
  for m in range((4 if typ==0 else 3)*k+1,(6 if typ==0 else 4)*k):
   if gcd(k,m)!=1:continue
   v,seq,F=gluing(3,k,m,[3*k,4*k,m])
   if len({x%3 for x in seq[:3]})<3:w={'rank':1,'triple':seq[:3]}
   else:
    off=3*k if typ==0 or m-3*k>=3 else 4*k
    for h in [F,F-off]:assert h>2 and all(v[h+d] for d in [-2,-1,1,2])
    w=boundary(seq,F) or boundary(seq,F-off)
   assert w and w in failures(seq)
   counts[label]+=1;examples.setdefault(label,w)
for s in range(6,101):
 for b in range(2*s+1,3*s):
  if gcd(s,b)!=1:continue
  v,seq,F=gluing(2,s,b,[2*s,b,3*s]);e=b-2*s;f=3*s-b
  source=(e==1 and s%3==2) or (e==2 and s%6==1)
  bad=failures(seq);assert bool(bad)!=source,(s,b)
  if not source:
   if len({x%3 for x in seq[:3]})<3:w={'rank':1,'triple':seq[:3]}
   elif f<=2:
    assert seq[9:12]==[7*s-f,7*s,8*s-2*f]
    w={'rank':10,'triple':seq[9:12]}
   else:
    assert e>=3
    hs=[F,F-2*s,F-3*s,F-4*s]
    for h in hs:assert h>2 and all(v[h+d] for d in [-2,-1,1,2])
    w=next(boundary(seq,h) for h in hs if boundary(seq,h))
   assert w in bad
   examples.setdefault('3a=2d',dict(s=s,b=b,**w))
  counts['3a=2d']+=1
for a in range(12,121):
 for t in range(1,(a+1)//2):
  if gcd(a,t)!=1:continue
  v,seq=actual([a,a+t,2*a-t]);A=[0]*a
  for j in range(a):A[j*t%a]=min(j*(a+t),(a-j)*(2*a-t))
  assert A==[min(n for n in range(r,len(v),a) if v[n]) for r in range(a)]
  source=(t==1 and a%3==0) or (t==2 and a%6==3)
  assert bool(failures(seq))!=source
  counts['3a=b+d']+=1
result=dict(counts=counts,examples=examples,intersections=intersections(),limits='Finite tests validate code, never universal necessity.')
(L/'checks.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(counts))
