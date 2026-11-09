"""Independent exact cell decomposition and Boolean-semigroup regressions. No author imports."""
from fractions import Fraction as Q
from math import gcd
from pathlib import Path
import json
L=Path(__file__).resolve().parent
def cells(kind):
 # Enumerate actual sums of <=12 generators; coordinates are coefficients of a,t.
 gs=[(1,0),(0,2),(0,3)] if kind=='A' else [(1,0),(1,1),(0,3)]
 forms={(0,0)}
 for _ in range(12):forms |= {(i+p,j+q) for i,j in forms for p,q in gs}
 forms=sorted(forms)
 events={Q(1,2),Q(2,3)}
 for i,j in forms:
  for p,q in forms+[(12,0)]:
   if j!=q:
    x=Q(p-i,j-q)
    if Q(1,2)<x<Q(2,3):events.add(x)
 events=sorted(events)
 def good(x):
  groups={}
  for i,j in forms:
   z=i+j*x
   if 0<z<=12:groups.setdefault(z,[]).append((i,j))
  rows=[groups[z] for z in sorted(groups)]
  out=[]
  for a in range(3):
   for t in range(3):
    rs=[{(i*a+j*t)%3 for i,j in row} for row in rows]
    if any(len(z)!=1 for z in rs):continue
    r=[next(iter(z)) for z in rs]
    if all(len(set(r[n:n+3]))==3 for n in range(0,len(r)-2,3)):out.append([a,t])
  return out
 intervals=[];vertices=[]
 for x,y in zip(events,events[1:]):
  r=good((x+y)/2)
  if r:intervals.append([str(x),str(y),r])
 for x in events[1:-1]:
  r=good(x)
  if r:vertices.append([str(x),r])
 expected=[['1/2','12/23'],['12/23','11/21'],['9/17','8/15'],['6/11','11/20'],['11/20','5/9']]
 if [r[:2] for r in intervals]!=expected:print(kind,'intervals',intervals,'vertices',vertices,flush=True)
 assert [r[:2] for r in intervals]==expected
 vs=['10/19','7/13','11/20','4/7','5/8']+(['12/23'] if kind=='B' else [])
 assert {r[0] for r in vertices}==set(vs)
 assert all(rs==[[1,1],[2,2]] for _,_,rs in intervals)
 return dict(events=len(events),intervals=intervals,vertices=vertices)
def dp(gs):
 a=min(gs);reachable=[True];run=0
 while run<a+8:
  n=len(reachable);v=any(n>=g and reachable[n-g] for g in gs)
  reachable.append(v);run=run+1 if v else 0
 # Run establishes conductor; append enough full periods to test aligned tail.
 reachable += [True]*(3*a+9)
 return reachable
def bad_in(v,lo,hi):
 seq=[n for n in range(1,len(v)) if v[n]]
 for p in range(0,len(seq)-2,3):
  tri=seq[p:p+3]
  if tri[0]>=lo and tri[-1]<=hi and len({n%3 for n in tri})<3:return dict(rank=p+1,triple=tri)
 return None
def reviews():
 counts={};examples={}
 for kind in ['A','B']:
  count=0
  for t in range(7,121):
   for a in range(12,2*t):
    if not 3*t<2*a or gcd(a,t)!=1:continue
    gs=[a,2*t,3*t] if kind=='A' else [a,a+t,3*t]
    v=dp(gs);table=[min(n for n in range(r,len(v),a) if v[n]) for r in range(a)]
    theoretical=[0]*a
    for j in range(a):theoretical[j*t%a]=((a+1)*t if j==1 else j*t) if kind=='A' else (j%3)*a+j*t
    assert table==theoretical
    F=max(table)-a
    gaps={n for n in range(1,F+1) if not v[n]}
    if kind=='A':
     predicted={F-i*a-j*t for j in [0]+list(range(2,a)) for i in range(F//a+1) if F-i*a-j*t>0}
    else:
     predicted={table[r]-i*a for r in range(a) for i in range(1,table[r]//a+1) if table[r]-i*a>0}
    assert gaps==predicted
    s=2*t-a;source=(s==1 and t%3==1) or (s==2 and t%6==5)
    witness=bad_in(v,1,len(v)-1)
    assert bool(witness)!=source
    if not source:
     found=bad_in(v,1,12*a)
     if not found:
      assert t>=5*s and s>=3 and a%3==t%3!=0
      low=F-(4*t if kind=='A' else 2*a if a%3==1 else a)-3
      found=bad_in(v,low,F+3)
      assert found,(kind,a,t)
      examples.setdefault(kind,dict(a=a,t=t,**found))
    count+=1
  counts[kind]=count
 return dict(counts=counts,top_examples=examples)
FAMILIES=[(3,0,3,1,6,-1),(6,1,6,2,9,3),(6,1,9,2,9,3),(6,1,6,3,6,5),(6,1,12,-4,12,0),(3,1,6,-1,6,0),(3,2,3,3,3,4),(12,2,12,4,18,3),(3,2,6,1,6,3),(6,3,6,5,12,4),(6,4,6,5,9,6),(12,4,18,3,18,5),(6,5,9,6,9,7),(6,5,12,4,12,6),(12,8,12,10,18,15),(12,8,18,13,18,15)]
def intersections():
 out=[]
 for h,row in enumerate(FAMILIES,1):
  a,A,b,B,d,D=row
  for label,c,C in [('4a=3b',4*a-3*b,4*A-3*B),('4a=3d',4*a-3*d,4*A-3*D)]:
   assert c!=0 or C!=0
   root=None if c==0 else -Q(C,c)
   admissible=root is not None and root.denominator==1 and root>=(2 if h==5 else 1)
   triple=[a*root+A,b*root+B,d*root+D] if admissible else None
   retained=bool(admissible and triple[0]>=12 and triple[0]<triple[1]<triple[2]<2*triple[0] and gcd(*map(int,triple))==1)
   assert not retained
   out.append(dict(H=h,support=label,coefficient=c,constant=C,root=str(root),source_parameter=bool(admissible),triple=list(map(str,triple)) if triple else None,retained=retained))
 return out
def empty_supports():
 counts=[0,0];examples={}
 for k in range(4,55):
  for typ in range(2):
   for m in range((4 if typ==0 else 3)*k+1,(6 if typ==0 else 4)*k):
    if gcd(k,m)!=1:continue
    gs=[3*k,4*k,m];v=dp(gs);F=(k-1)*m+5*k
    assert max(n for n in range(len(v)) if not v[n])==F
    constructive=construct(k,m,typ)
    seq=[n for n in range(1,len(v)) if v[n]]
    p=constructive['rank']-1
    assert p%3==0 and seq[p:p+3]==constructive['triple']
    assert len({n%3 for n in constructive['triple']})<3
    for n in range(len(v)):
     j=n*pow(m,-1,k)%k;z=(n-j*m)//k
     assert v[n]==(z>=0 and z not in [1,2,5])
    w=bad_in(v,max(1,F-4*k-3),F+3)
    assert w,(k,m,typ)
    examples.setdefault(str(typ),dict(k=k,m=m,**w));counts[typ]+=1
 return dict(counts=counts,examples=examples)
def construct(k,m,typ):
 gs=sorted([3*k,4*k,m])
 if len({n%3 for n in gs})<3:return dict(rank=1,triple=gs)
 F=(k-1)*m+5*k
 def rank(n):
  total=0
  for j in range(k):
   z=(n-j*m)//k
   if z>=0:total+=z+1-sum(g<=z for g in [1,2,5])
  return total-1
 offsets=[0,3*k] if typ==0 or m-3*k>=3 else [0,4*k]
 for off in offsets:
  h=F-off;r=rank(h-1)
  if r%3==1:return dict(rank=r,triple=[h-1,h+1,h+2])
  if r%3==2:return dict(rank=r-1,triple=[h-2,h-1,h+1])
 raise AssertionError((k,m,typ,'universal boundary contradiction failed'))
result=dict(ratio={k:cells(k) for k in ['A','B']},review=reviews(),intersections=intersections(),empty_supports=empty_supports())
(L/'checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['ratio','intersections']}))
