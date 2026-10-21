# Original r153 diagnostic, MIT. Exact fractions; stdout only; finite scope.
from fractions import Fraction as F
from itertools import product
import random,json

def solve(a,b):
 n=len(a);k=len(b[0]);aug=[list(a[i])+list(b[i]) for i in range(n)]
 for i in range(n):
  j=next(j for j in range(i,n) if aug[j][i]);aug[i],aug[j]=aug[j],aug[i]
  q=aug[i][i];aug[i]=[v/q for v in aug[i]]
  for j in range(n):
   if j!=i:
    q=aug[j][i];aug[j]=[x-q*y for x,y in zip(aug[j],aug[i])]
 return [row[n:] for row in aug]

def absorb(q,b):
 # Least nonnegative exit solution: kill rows with no path to an output.
 n=len(q);k=len(b[0]);good={i for i in range(n) if any(b[i])}
 while True:
  new=good|{i for i in range(n) if any(q[i][j] for j in good)}
  if new==good:break
  good=new
 ix=sorted(good);out=[[F(0) for _ in range(k)] for _ in range(n)]
 if ix:
  a=[[F(i==j)-q[i][j] for j in ix] for i in ix]
  ans=solve(a,[b[i] for i in ix])
  for i,row in zip(ix,ans):out[i]=row
 return out

def concat(blocks):
 # Each segment has two entry rows, four outputs: left,right,accept,reject.
 n=len(blocks);q=[[F(0) for _ in range(2*n)] for _ in range(2*n)]
 b=[[F(0) for _ in range(4)] for _ in range(2*n)]
 for i,seg in enumerate(blocks):
  for side,row in enumerate(seg):
   j=2*i+side
   if i==0:b[j][0]=row[0]
   else:q[j][2*(i-1)+1]=row[0]
   if i==n-1:b[j][1]=row[1]
   else:q[j][2*(i+1)]=row[1]
   b[j][2:]=row[2:]
 a=absorb(q,b);return [a[0],a[-1]]

def compose(a,b):
 la,fa,aa,ra=a[0];ba,rra,ab,rb=a[1]
 lb,fb,ac,rc=b[0];bb,rrb,ad,rd=b[1]
 den=1-lb*rra
 def loop(x,y):
  if den:return x*y/den
  assert x*y==0
  return F(0)
 return [[la+loop(fa,lb*ba),loop(fa,fb),aa+loop(fa,ac+lb*ab),ra+loop(fa,rc+lb*rb)],
         [loop(bb,ba),rrb+loop(bb,rra*fb),ad+loop(bb,ab+rra*ac),rd+loop(bb,rb+rra*rc)]]

def forests(q,b,start=0):
 # Two terminal labels, all transient vertices choose one outgoing edge.
 n=len(q);den=F(0);num=F(0)
 for dest in product(range(n+2),repeat=n):
  weight=F(1);roots=[];valid=True
  for i,j in enumerate(dest):weight*=q[i][j] if j<n else b[i][j-n]
  if not weight:continue
  for i in range(n):
   seen=set();j=i
   while j<n and j not in seen:seen.add(j);j=dest[j]
   if j<n:valid=False;break
   roots.append(j)
  if valid:
   den+=weight
   if roots[start]==n:num+=weight
 return num/den

rng=random.Random(153)
def seg():
 rows=[]
 for _ in range(2):
  a=[rng.randrange(0,8) for _ in range(4)];d=sum(a)+rng.randrange(1,8)
  rows.append([F(x,d) for x in a])
 return rows
segments=[seg() for _ in range(15)]
# A trapped join tests the singular case and nonhalting deficit.
segments += [[[F(0),F(1),F(0),F(0)],[F(0),F(1),F(0),F(0)]],
             [[F(1),F(0),F(0),F(0)],[F(1),F(0),F(0),F(0)]],
             [[F(0)]*4,[F(0)]*4]]
pairs=0;triples=0
for a,b in product(segments,repeat=2):
 assert compose(a,b)==concat([a,b]);pairs+=1
for _ in range(120):
 a,b,c=[rng.choice(segments) for _ in range(3)]
 assert compose(compose(a,b),c)==compose(a,compose(b,c))==concat([a,b,c]);triples+=1
forest_cases=0
for n in [1,2,3]:
 for _ in range(24):
  rows=[]
  for i in range(n):
   x=[rng.randrange(1,7) for _ in range(n+2)];rows.append([F(v,sum(x)) for v in x])
  q=[x[:n] for x in rows];b=[x[n:] for x in rows]
  assert forests(q,b)==absorb(q,b)[0][0];forest_cases+=1
# Exact full-relation path counts; this is a diagnostic of credited restart.
h=2;relations=[[(m>>(2*i+j))&1 for i in range(2) for j in range(2)] for m in range(16)]
counts=0;live=0
for length in range(4):
 for word in product(relations,repeat=length):
  v=[1,1]
  for r in word:v=[sum(v[i]*r[2*i+j] for i in range(2)) for j in range(2)]
  N=sum(v);Q=2**(length+1);a=F(N,2*Q);b=F(1,4*Q)
  ans=absorb([[1-a-b]],[[a,b]])[0][0]
  assert ans==F(2*N,2*N+1)
  assert (ans>=F(2,3)) if N else ans==0
  counts+=1;live+=bool(N)
# A layered undirected walk can reach the last layer without a directed path.
rels=[{(0,0)},{(0,0),(1,0),(1,1)},{(1,0)}]
reach={0,1}
for r in rels:reach={b for a,b in r if a in reach}
assert not reach
route=[(0,0),(1,0),(2,0),(1,1),(2,1),(3,0)]
for x,y in zip(route,route[1:]):
 a,b=sorted([x,y]);assert b[0]==a[0]+1 and (a[1],b[1]) in rels[a[0]]
cliffs=[]
for k in [2,4,8,16]:
 u=F(1,2**k);p=absorb([[1-u-u*u]],[[u,u*u]])[0][0]
 r=absorb([[1-u-u*u]],[[u*u,u]])[0][0]
 assert p==1/(1+u) and r==u/(1+u)
 cliffs.append({'u':str(u),'accept_1':str(p),'accept_2':str(r)})
print(json.dumps({'scope':'finite diagnostic only; no mathematical or contribution gate',
 'segment_pairs':pairs,'associative_triples':triples,'forest_identity_cases':forest_cases,
 'restart_relation_words_h2_length_le3':counts,'live_words':live,
 'singular_join_included':True,'undirected_false_positive_route':route,'return_cliffs':cliffs},indent=2))
