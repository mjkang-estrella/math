# Exact finite derivation for one type-A interval, not a test of stipulated upstream truth.
from fractions import Fraction as Q
from itertools import permutations,combinations
from functools import lru_cache
from pathlib import Path
import json,time
OUT=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r157/receipts/finite-bmp.json')
START=time.monotonic()
ZERO=(0,0,0)
def add(a,b):
 c=a.copy()
 for m,v in b.items():
  c[m]=c.get(m,0)+v
  if not c[m]:del c[m]
 return c
def scale(a,c):return {m:v*c for m,v in a.items() if v*c}
def mul(a,b):
 c={}
 for m,v in a.items():
  for n,w in b.items():c=add(c,{tuple(x+y for x,y in zip(m,n)):v*w})
 return c
@lru_cache(None)
def mons(d,avoid=-1):
 if d<0:return ()
 return tuple((a,b,d-a-b) for a in range(d+1) for b in range(d-a+1) if (a,b,d-a-b)[avoid]==0) if avoid>=0 else tuple((a,b,d-a-b) for a in range(d+1) for b in range(d-a+1))
def linear(i):return {tuple(int(j==i) for j in range(3)):Q(1)}
X=[linear(i) for i in range(3)]
@lru_cache(None)
def redmon(m,root):
 pivot=root[0];p={ZERO:Q(1)}
 sub={}
 for i in root[1:]:sub=add(sub,scale(X[i],-1))
 for _ in range(m[pivot]):p=mul(p,sub)
 other=tuple(0 if i==pivot else a for i,a in enumerate(m))
 return mul(p,{other:Q(1)})
def reduce(p,root):
 out={}
 for m,c in p.items():out=add(out,scale(redmon(m,root),c))
 return out
class Span:
 def __init__(self):self.rows={}
 def insert(self,v):
  v=list(map(Q,v))
  for p,b in sorted(self.rows.items()):
   if v[p]:
    c=v[p];v=[a-c*z for a,z in zip(v,b)]
  p=next((i for i,a in enumerate(v) if a),None)
  if p is None:return False
  c=v[p];self.rows[p]=[a/c for a in v];return True
 def rank(self):return len(self.rows)
def nullspace(rows,n):
 sp=Span()
 for row in rows:sp.insert(row)
 out=[]
 for f in range(n):
  if f in sp.rows:continue
  v=[Q(0)]*n;v[f]=Q(1)
  for p,b in sorted(sp.rows.items(),reverse=True):v[p]=-sum(b[j]*v[j] for j in range(p+1,n))
  out.append(v)
 return out
def length(w):return sum(w[i]>w[j] for i in range(4) for j in range(i+1,4))
def leq(a,b):return all(sorted(a[:i])[j]<=sorted(b[:i])[j] for i in range(1,5) for j in range(i))
def swapval(w,i,j):return tuple(j if v==i else i if v==j else v for v in w)
def edge(a,b):
 pairs=[(i,j) for i in range(1,5) for j in range(i+1,5) if swapval(a,i,j)==b]
 return tuple(range(pairs[0][0]-1,pairs[0][1]-1)) if pairs and length(a)<length(b) else None
W=tuple(permutations(range(1,5)));TOP=(3,4,1,2)
V=sorted([w for w in W if leq(w,TOP)],key=lambda w:(-length(w),w))
UP={a:[b for b in V if edge(a,b)] for a in V}
# Polynomial-in-q routines.
def padd(a,b):
 n=max(len(a),len(b));c=[(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(n)]
 while len(c)>1 and c[-1]==0:c.pop()
 return tuple(c)
def pmul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return padd(tuple(c),(0,))
@lru_cache(None)
def R(a,b):
 if not leq(a,b):return (0,)
 if a==b:return (1,)
 s=next(i for i in range(1,4) if length(swapval(b,i,i+1))<length(b));sa=swapval(a,s,s+1);sb=swapval(b,s,s+1)
 return R(sa,sb) if length(sa)<length(a) else padd(pmul((-1,1),R(a,sb)),pmul((0,1),R(sa,sb)))
@lru_cache(None)
def P(a,b):
 if not leq(a,b):return (0,)
 if a==b:return (1,)
 d=length(b)-length(a);t=(0,)
 for z in W:
  if z!=a and leq(a,z) and leq(z,b):t=padd(t,pmul(R(a,z),P(z,b)))
 return padd(tuple(-t[k] if k<len(t) else 0 for k in range((d+1)//2)),(0,))
ST={TOP:[0]};MAP={}
def basis(a,d):return [(g,m) for g,s in enumerate(ST[a]) for m in mons(d-s)]
def ebasis(a,b,d):return [(g,m) for g,s in enumerate(ST[b]) for m in mons(d-s,edge(a,b)[0])]
def action(a,b,g,m):return [reduce(mul(p,{m:Q(1)}),edge(a,b)) for p in MAP[a,b][g]]
def vecpolys(v,bs,num):
 ps=[{} for _ in range(num)]
 for c,(g,m) in zip(v,bs):
  if c:ps[g][m]=c
 return ps
for x in V[1:]:
 upper=[a for a in V if a!=x and leq(x,a)]
 ST[x]=[]
 for y in UP[x]:MAP[x,y]=[]
 for d in range(2):
  sb=[(a,g,m) for a in upper for g,m in basis(a,d)];idx={p:i for i,p in enumerate(sb)}
  rows=[]
  for a in upper:
   for b in UP[a]:
    eb=ebasis(a,b,d);ei={z:i for i,z in enumerate(eb)};rr=[[Q(0)]*len(sb) for _ in eb]
    for g,m in basis(a,d):
     for h,poly in enumerate(action(a,b,g,m)):
      for n,c in poly.items():rr[ei[h,n]][idx[a,g,m]]+=c
    for g,m in basis(b,d):
     for n,c in reduce({m:Q(1)},edge(a,b)).items():rr[ei[g,n]][idx[b,g,m]]-=c
    rows+=rr
  ns=nullspace(rows,len(sb))
  bb=[(y,g,m) for y in UP[x] for g,m in ebasis(x,y,d)];bi={v:i for i,v in enumerate(bb)}
  boundary=[]
  for v in ns:
   bv=[Q(0)]*len(bb)
   for y in UP[x]:
    for g,m in basis(y,d):
     for n,c in reduce({m:Q(1)},edge(x,y)).items():bv[bi[y,g,n]]+=v[idx[y,g,m]]*c
   boundary.append(bv)
  span=Span()
  for gen,degree in enumerate(ST[x]):
   for m in mons(d-degree):
    vec=[Q(0)]*len(bb)
    for y in UP[x]:
     for h,poly in enumerate(action(x,y,gen,m)):
      for n,c in poly.items():vec[bi[y,h,n]]=c
    span.insert(vec)
  for v in boundary:
   if span.insert(v):
    ST[x].append(d)
    for y in UP[x]:
     eb=ebasis(x,y,d);sv=[v[bi[y,g,m]] for g,m in eb];MAP[x,y].append(vecpolys(sv,eb,len(ST[y])))
 assert ST[x]==[d for d,c in enumerate(P(x,TOP)) for _ in range(c)],(x,ST[x],P(x,TOP))
 if time.monotonic()-START>40:raise RuntimeError('construction timeout')
# Analyze every subset at both singular stalks in degrees 0..5.
results=[]
for x in V:
 if len(ST[x])<2:continue
 for mask in range(1<<len(UP[x])):
  F=[y for i,y in enumerate(UP[x]) if mask>>i&1];dims=[];mingens=[];prev=[];prevbs=[]
  for d in range(6):
   bs=basis(x,d);eb=[(y,g,m) for y in F for g,m in ebasis(x,y,d)];ei={z:i for i,z in enumerate(eb)};rows=[[Q(0)]*len(bs) for _ in eb]
   for col,(g,m) in enumerate(bs):
    for y in F:
     for h,poly in enumerate(action(x,y,g,m)):
      for n,c in poly.items():rows[ei[y,h,n]][col]+=c
   ker=nullspace(rows,len(bs));dims.append(len(ker));sp=Span();bidx={p:i for i,p in enumerate(bs)}
   for v in prev:
    for k in range(3):
     w=[Q(0)]*len(bs)
     for c,(g,m) in zip(v,prevbs):
      n=list(m);n[k]+=1;w[bidx[g,tuple(n)]]+=c
     sp.insert(w)
   mingens.append(len(ker)-sp.rank());prev=ker;prevbs=bs
  numerator=[sum((-1)**j*[1,3,3,1][j]*dims[d-j] for j in range(min(d,3)+1)) for d in range(6)]
  results.append({'x':x,'F':F,'dims_degrees0to5':dims,'minimal_generators_degrees0to5':mingens,'numerator_coeffs_degrees0to5':numerator,'nonfree_certificate':sum(mingens)>len(ST[x])})
  if time.monotonic()-START>110:raise RuntimeError('finite calculation timeout')
def polystr(p):return {','.join(map(str,m)):str(c) for m,c in p.items()}
out={'scope':'S4, top3412, all subsets at both singular stalks, exact rational degrees0..5; no global bound inferred','vertices':V,'stalks':[{'x':x,'P':P(x,TOP),'degrees':ST[x]} for x in V],'maps':[{'x':x,'y':y,'root_simple_coordinates':edge(x,y),'generator_images':[[polystr(p) for p in gen] for gen in MAP[x,y]]} for x in V for y in UP[x]],'subset_results':results,'elapsed':time.monotonic()-START}
OUT.write_text(json.dumps(out,indent=2)+'\n')
print('vertices',len(V),'subsets',len(results),'nonfree',sum(r['nonfree_certificate'] for r in results),'elapsed',out['elapsed'])
for r in results:
 if r['nonfree_certificate']:print(r)
