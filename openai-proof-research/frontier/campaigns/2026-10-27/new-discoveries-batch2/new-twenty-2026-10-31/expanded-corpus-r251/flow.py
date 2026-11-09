from pathlib import Path
from functools import lru_cache
import json
L=Path(__file__).resolve().parent
K={(0,0):-1,(1,0):1,(0,1):1,(1,1):-1}
def add(a,b):
 c=a.copy()
 for x,v in b.items():c[x]=c.get(x,0)+v
 return {x:v for x,v in c.items() if v}
def mul(a,b):
 c={}
 for (i,j),v in a.items():
  for (k,l),w in b.items():c[(i+k,j+l)]=c.get((i+k,j+l),0)+v*w
 return {x:v for x,v in c.items() if v}
@lru_cache(None)
def row(bs):
 r=sum(b>0 for b in bs);p={(0,0):1}
 for b in bs:
  if b:p=mul(p,{(b-1-j,j):1 for j in range(b)})
 for _ in range(r-1):p=mul(p,K)
 return p
def comp(s,r):
 if r==1:yield (s,);return
 for a in range(s+1):
  for b in comp(s-a,r-1):yield (a,)+b
def graph(mask,n):
 E={(i,j) for j in range(1,n+1) for i in range(j) if mask>>(j-1)&1}
 ds=[sum(i in e for e in E) for i in range(n+1)];order=sorted(range(n+1),key=lambda i:(-ds[i],i));inv={v:i for i,v in enumerate(order)}
 return frozenset(tuple(sorted((inv[a],inv[b]))) for a,b in E)
def poly(E,n):
 @lru_cache(None)
 def go(v,stock):
  if v==0:return {(0,0):1}
  ns=[j for j in range(v) if (j,v) in E];out={}
  for bs in comp(stock[v],len(ns)):
   st=list(stock[:v]);
   for j,b in zip(ns,bs):st[j]+=b
   out=add(out,mul(row(bs),go(v-1,tuple(st))))
  return out
 return go(n,tuple([0]+[1]*n))
rows=[];Ps={};n=10
for mask in range(1<<n):
 if not mask>>(n-1)&1:continue
 E=graph(mask,n)
 if len(E)>18:continue
 P=poly(E,n);Ps[E]=P
 rows.append({'mask':mask,'edges':sorted(E),'coefficients':[[i,j,c] for (i,j),c in sorted(P.items())],'negative_coefficients':sum(c<0 for c in P.values())})
 print('mask',mask,'edges',len(E),'terms',len(P),flush=True)
pairs=[]
for E,P in Ps.items():
 for F,Q in Ps.items():
  if F<E:
   diff=add(P,{x:-v for x,v in Q.items()});bad=[[i,j,c] for (i,j),c in diff.items() if c<0]
   pairs.append({'lower_edges':sorted(F),'upper_edges':sorted(E),'negative_coefficients':bad})
(L/'flow-results.json').write_text(json.dumps({'n':n,'edge_bound':18,'graphs':rows,'comparable_pairs':pairs},indent=2));print('graphs',len(rows),'pairs',len(pairs),'failed',sum(bool(p['negative_coefficients']) for p in pairs))
