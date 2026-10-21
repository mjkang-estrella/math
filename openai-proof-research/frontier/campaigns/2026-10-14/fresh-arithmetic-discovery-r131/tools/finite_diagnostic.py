"""Bounded exact diagnostic, not a universal mathematical gate. Run at project root."""
from itertools import permutations
from collections import defaultdict
from math import factorial
from pathlib import Path
import json
ROOT=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r131')
def vp(n,p):
 if n==0:return None
 a=0
 while n%p==0:a+=1;n//=p
 return a
out=[]
for degree,p,even in [(3,2,False),(4,3,True)]:
 G=[g for g in permutations(range(degree)) if not even or sum(g[i]>g[j] for i in range(degree) for j in range(i+1,degree))%2==0]
 ix={g:i for i,g in enumerate(G)}; one=ix[tuple(range(degree))];m=len(G)
 mul=[[ix[tuple(g[h[i]] for i in range(degree))] for h in G] for g in G]
 inv=[next(j for j in range(m) if mul[i][j]==one) for i in range(m)]
 def closure(s):
  s=set(s)|{one}
  while True:
   t=s|{mul[a][b] for a in s for b in s}
   if len(t)==len(s):return frozenset(s)
   s=t
 subs={closure([])}
 while True:
  nxt=subs|{closure(set(h)|{g}) for h in subs for g in range(m)}
  if nxt==subs:break
  subs=nxt
 normalp=[h for h in subs if len(h)>1 and p**vp(len(h),p)==len(h) and all(mul[mul[g][a]][inv[g]] in h for g in range(m) for a in h)]
 assert not normalp
 classes=[];left=set(range(m))
 while left:
  g=min(left);c={mul[mul[x][g]][inv[x]] for x in range(m)};classes.append(sorted(c));left-=c
 def order(g):
  v=one
  for n in range(1,m+1):
   v=mul[v][g]
   if v==one:return n
 classes.sort(key=lambda c:(order(c[0]),len(c),c[0]))
 hs=sorted(subs,key=lambda h:(len(h),tuple(sorted(h))));hi={h:i for i,h in enumerate(hs)};full=hi[frozenset(range(m))]
 join=[[hi[closure(set(h)|{g})] for g in range(m)] for h in hs]
 handles=[]
 for x in range(m):
  for y in range(m):
   comm=mul[mul[mul[x][y]][inv[x]]][inv[y]];handles.append((inv[comm],hi[closure([x,y])]))
 # Each specified word is counted by dynamic programming on its product and generated subgroup.
 cases=[]
 if m==6:
  cases=[(0,2,0),(0,6,0),(0,12,0),(2,2,2),(4,4,4),(1,2,3),(2,4,6),(0,2,10)]
 else:
  cases=[(0,0,3,0),(0,0,6,0),(0,0,9,0),(0,3,3,0),(3,3,3,0),(0,0,3,3),(3,3,3,3),(0,6,6,6)]
 for bs in cases:
  assert len(bs)==len(classes)
  assert any(b and order(c[0])%p==0 for b,c in zip(bs,classes))
  total=0
  for target,start in handles:
   counts={(one,start):1}
   for c,b in zip(classes,bs):
    for _ in range(b):
     new=defaultdict(int)
     for (prod,h),value in counts.items():
      for u in c:new[(mul[prod][u],join[h][u])]+=value
     counts=new
   total+=counts.get((target,full),0)
  center=[z for z in range(m) if all(mul[z][g]==mul[g][z] for g in range(m))];D=m//len(center);assert total%D==0
  fixed=total//D;N=sum(bs);mult=factorial(N)
  for b in bs:mult//=factorial(b)
  # The sequential factorial division above is exact for this product division as an integer.
  assert mult*__import__('functools').reduce(lambda a,b:a*factorial(b),bs,1)==factorial(N)
  count=fixed*mult;a=max(vp(order(g),p) for g in range(m));bound=max(0,vp(N,p)-a-vp(m,p)+2);value=vp(count,p)
  assert value is None or value>=bound
  out.append({'group':'S3' if m==6 else 'A4','p':p,'class_orders':[order(c[0]) for c in classes],'multiplicities':bs,'N':N,'fixed_word_orbits':fixed,'multinomial':mult,'multiset_orbits':count,'valuation':value,'bound':bound})
# Exercise exact ramification recurrence independently of group tables.
from fractions import Fraction
checks=0
for p in [2,3,5,7]:
 for e in range(1,65):
  k0=0
  while (p-1)*p**k0<e:k0+=1
  v=Fraction(1,e)
  for k in range(17):
   assert v>=k-k0+Fraction(1,e)
   assert Fraction(p**k,e)>=k-k0+Fraction(1,e)
   v=min(p*v,v+1);checks+=1
(ROOT/'notes/finite-diagnostic.json').write_text(json.dumps({'scope':'Finite arithmetic diagnostics only; no universal proof or independent verdict.','tuple_cases':out,'recurrence_cases':checks},indent=2)+'\n')
print('Tuple cases',len(out),'exact recurrence cases',checks,'all satisfied stated diagnostics')
