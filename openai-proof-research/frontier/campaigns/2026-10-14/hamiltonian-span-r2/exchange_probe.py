# Copyright (c) 2026 Myeongjin Kang. MIT.
"""New finite diagnostic; no imports from frozen packages; only stdout writes."""
from itertools import combinations
from fractions import Fraction
import random,json

def prism(m):
 e={tuple(sorted(z)) for i in range(m) for z in [(i,(i+1)%m),(m+i,m+(i+1)%m),(i,m+i)]}
 return 2*m,sorted(e),[list(range(m)),list(range(m,2*m))]+[[i,(i+1)%m,m+(i+1)%m,m+i] for i in range(m)]
def expand(g,fi,i,j):
 n,e,fs=g;f=fs[fi];l=len(f);u,v,y,x=f[i],f[(i+1)%l],f[j],f[(j+1)%l]
 a,b,d,c=range(n,n+4);rem={tuple(sorted((u,v))),tuple(sorted((x,y)))}
 ring=[(a,b),(b,d),(d,c),(c,a)];spokes=[(u,a),(v,b),(y,d),(x,c)]
 ne=sorted({tuple(sorted(z)) for z in e if z not in rem}|{tuple(sorted(z)) for z in ring+spokes})
 nf=[]
 for k,h in enumerate(fs):
  if k==fi:continue
  z=[]
  for p,q in zip(h,h[1:]+h[:1]):
   z.append(p)
   if {p,q}=={u,v}:z.extend([a,b] if p==u else [b,a])
   if {p,q}=={x,y}:z.extend([c,d] if p==x else [d,c])
  nf.append(z)
 def seg(start,end):
  out=[f[start%l]]
  while start%l!=end%l:start+=1;out.append(f[start%l])
  return out
 nf.extend([[a,b,d,c],seg(i+1,j)+[d,b],seg(j+1,i)+[a,c]])
 return (n+4,ne,nf),{'old_n':n,'removed':sorted(rem),'ring':[tuple(sorted(z)) for z in ring],'spokes':[tuple(sorted(z)) for z in spokes]}
def matchings(n,e):
 adj=[[] for _ in range(n)]
 for k,(u,v) in enumerate(e):adj[u].append((v,k));adj[v].append((u,k))
 def rec(mask,bits):
  if not mask:yield bits;return
  u=(mask&-mask).bit_length()-1
  for v,k in adj[u]:
   if mask>>v&1:yield from rec(mask^(1<<u)^(1<<v),bits|(1<<k))
 yield from rec((1<<n)-1,0)
def hcs(g):
 n,e=g[:2];allbits=(1<<len(e))-1
 for m in matchings(n,e):
  h=allbits^m;adj=[[] for _ in range(n)]
  for k,(u,v) in enumerate(e):
   if h>>k&1:adj[u].append(v);adj[v].append(u)
  seen={0};todo=[0]
  while todo:
   for v in adj[todo.pop()]:
    if v not in seen:seen.add(v);todo.append(v)
  if len(seen)==n:yield h

def vector(bits,m):return [(bits>>k)&1 for k in range(m)]
def rank(rows):
 piv={}
 for row in rows:
  row=list(map(Fraction,row))
  for j,b in sorted(piv.items()):
   q=row[j]
   if q:row=[x-q*y for x,y in zip(row,b)]
  j=next((j for j,x in enumerate(row) if x),None)
  if j is not None:
   q=row[j];piv[j]=[x/q for x in row]
 return len(piv)
def classify(h,ring,spokes):
 used=[i for i,k in enumerate(spokes) if h>>k&1]
 if len(used)==2:
  i=next(i for i in range(4) if set(used)=={i,(i+1)%4});return i
 assert len(used)==4
 # P means exterior pairing (01)(23), hence internal matching (12)(30).
 return 4 if (h>>ring[1]&1) else 5

def validate(g):
 n,e,faces=g
 assert len(e)==3*n//2 and len(set(e))==len(e)
 adj=[set() for _ in range(n)]
 for u,v in e:
  assert 0<=u<v<n;adj[u].add(v);adj[v].add(u)
 assert all(len(z)==3 for z in adj)
 color={0:0};todo=[0]
 while todo:
  u=todo.pop()
  for v in adj[u]:
   if v not in color:color[v]=1-color[u];todo.append(v)
   else:assert color[v]!=color[u]
 assert len(color)==n
 for deleted in [()]+[(i,) for i in range(n)]+list(combinations(range(n),2)):
  remaining=set(range(n))-set(deleted);seen={min(remaining)};todo=list(seen)
  while todo:
   for v in adj[todo.pop()]&remaining-seen:seen.add(v);todo.append(v)
  assert seen==remaining
 assert n-len(e)+len(faces)==2
 counts={z:0 for z in e}
 for f in faces:
  assert len(set(f))==len(f) and len(f)%2==0
  for u,v in zip(f,f[1:]+f[:1]):counts[tuple(sorted((u,v)))]+=1
 assert set(counts.values())=={2}

def inspect(g,h,meta):
 validate(g);validate(h)
 n,e=h[:2];m=len(e);index={z:i for i,z in enumerate(e)}
 ring=[index[z] for z in meta['ring']];spokes=[index[z] for z in meta['spokes']]
 groups=[[] for _ in range(6)]
 for c in hcs(h):groups[classify(c,ring,spokes)].append(c)
 assert all(groups)
 old_e=g[1];old_kept=[(i,index[z]) for i,z in enumerate(old_e) if z not in meta['removed']]
 zeros=[]
 ringbits=sum(1<<k for k in ring)
 for c in hcs(g):
  if any(c>>old_e.index(z)&1 for z in meta['removed']):continue
  zeros.append(ringbits|sum(((c>>i)&1)<<j for i,j in old_kept))
 failure=[]
 for z in zeros:
  zv=vector(z,m);ok=False
  for i,j,k in [(0,2,4),(1,3,5)]:
   target=set(groups[j])
   for a in groups[i]:
    av=vector(a,m)
    for b in groups[k]:
     bv=vector(b,m);need=[x+y-t for x,y,t in zip(zv,bv,av)]
     if all(x in (0,1) for x in need) and sum(x<<q for q,x in enumerate(need)) in target:ok=True;break
    if ok:break
   if ok:break
  if not ok:failure.append(z)
 kept=[k for k in range(m) if k not in set(ring+spokes)]
 rep=[vector(s[0],m) for s in groups]
 W=[[((c>>k)&1)-rep[i][k] for k in kept] for i,s in enumerate(groups) for c in s[1:]]
 d=[rep[0][k]+rep[2][k]-rep[1][k]-rep[3][k]-rep[4][k]+rep[5][k] for k in kept]
 allc=sum(groups,[]);v0=vector(allc[0],m)
 ar=rank([[x-y for x,y in zip(vector(c,m),v0)] for c in allc[1:]])
 wr=rank(W);dr=rank(W+[d]);assert ar==4+dr
 return {'n':n,'cycles':len(allc),'groups':list(map(len,groups)),'zero_cycles':len(zeros),'three_cycle_resolution_failures':len(failure),'within_rank':wr,'with_hexagon_rank':dr,'full_rank':ar,'target':n//2+1},failure,groups

def main():
 rng=random.Random(161026)
 for m in [4,6,8,10,12]:
  g=prism(m);face=2;h,meta=expand(g,face,1,3)
  rec,fail,groups=inspect(g,h,meta);print(json.dumps({'case':'adjacent-rung-prism','m':m,**rec}),flush=True)
  if fail and m==4:print(json.dumps({'first_failed_resolution':fail[0],'graph':h,'parent':g,'meta':meta}),flush=True)
 for trial in range(16):
  g=prism(rng.choice([4,6,8]))
  for step in range(1+trial%3):
   options=[(fi,i,j) for fi,f in enumerate(g[2]) for i,j in combinations(range(len(f)),2) if (j-i)%2==0]
   h,meta=expand(g,*rng.choice(options));rec,fail,groups=inspect(g,h,meta)
   print(json.dumps({'case':'seeded','trial':trial,'step':step,**rec}),flush=True)
   assert rec['full_rank']==rec['target']
   g=h
if __name__=='__main__':main()
