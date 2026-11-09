from pathlib import Path
from heapq import heappush,heappop
from math import gcd
from functools import reduce
import json
L=Path(__file__).resolve().parent
def apery(g):
 m=g[0];a=[10**20]*m;a[0]=0;q=[(0,0)]
 while q:
  d,r=heappop(q)
  if d!=a[r]:continue
  for n in g[1:]:
   v=d+n;t=v%m
   if v<a[t]:a[t]=v;heappush(q,(v,t))
 return a
def fact(t,g):
 if not g:return [()] if t==0 else []
 if len(g)==1:return [(t//g[0],)] if t>=0 and t%g[0]==0 else []
 return [(i,)+v for i in range(t//g[0]+1) for v in fact(t-i*g[0],g[1:])]
def certificate(g):
 g=tuple(sorted(set(g)))
 if reduce(gcd,g)!=1 or len(g)!=4:return None
 if any(fact(n,g[:i]) for i,n in enumerate(g) if i):return None
 a=apery(g);m=g[0];F=max(a)-m
 mem=lambda n:n>=0 and n>=a[n%m]
 pf=sorted(w-m for w in a if all(mem(w-m+n) for n in g))
 # Independent finite DP membership: beyond F all integers are in S by Apéry.
 dp=[False]*(2*max(a)+max(g)+1);dp[0]=True
 for t in range(1,len(dp)):dp[t]=any(t>=n and dp[t-n] for n in g)
 assert all(dp[t]==mem(t) for t in range(len(dp)))
 direct=[t for t in range(F+1) if not dp[t] and all(dp[t+n] for n in g)]
 assert direct==pf
 canonical=all(mem(m+F-f) for f in pf)
 rows=[]; top=fact(max(a),g[1:])
 if canonical:
  for f in pf[:-1]:
   fac=fact(m+F-f,g[1:]);U=[i+1 for i in range(3) if any(v[i] for v in fac)]
   rf={}
   for i in range(1,4):
    reduced=g[:i]+g[i+1:];vs=fact(f+g[i],reduced)
    assert vs
    rf[str(i+1)]=vs
    if i in U:assert all(v[0]==0 for v in vs)
   for v in fac:
    assert not any(all(x<=y for x,y in zip(v,b)) for b in top)
    for j in range(3):
     if v[j]:
      pred=tuple(v[k]-(k==j) for k in range(3))
      assert any(all(x<=y for x,y in zip(pred,b)) for b in top)
   rows.append(dict(f=f,reflection=m+F-f,factorizations=fac,union_support=[i+1 for i in U],rf=rf))
  # Every pair of reflection factorizations is incomparable coordinatewise.
  for i,row in enumerate(rows):
   for other in rows[i+1:]:
    for u in row['factorizations']:
     for v in other['factorizations']:
      assert not all(x<=y for x,y in zip(u,v)) and not all(y<=x for x,y in zip(u,v))
  if len(top)==1:assert len(pf)<=4 and all(all(sum(x>0 for x in v)==1 for v in r['factorizations']) for r in rows)
 return dict(generators=g,apery=a,F=F,PF=pf,canonical=canonical,W_factorizations=top,rows=rows)
fixtures=[certificate(g) for g in [(16,17,19,39),(9,10,12,13),(15,17,28,41)]]
found={};count=0;can=0
# Four fixed deformations test structural claims; no general census or novelty credit.
for m in range(8,181):
 for g in [(m,m+1,m+3,2*m+7),(m,m+1,m+3,2*m-1),(m,m+2,m+5,2*m+3),(m,m+1,m+4,2*m+5)]:
  c=certificate(g)
  if c is None:continue
  count+=1
  if not c['canonical']:continue
  can+=1
  rs=c['rows']
  tests={'mixed_reflection':any(not any(sum(x>0 for x in v)==1 for v in r['factorizations']) for r in rs),
   'multiple_factorizations':any(len(r['factorizations'])>1 for r in rs),
   'full_union_support':any(len(r['union_support'])==3 for r in rs),
   'repeated_support':any(set(r['union_support'])==set(s['union_support']) for i,r in enumerate(rs) for s in rs[i+1:]),
   'type_at_least_five':len(c['PF'])>=5}
  for k,v in tests.items():
   if v and k not in found:found[k]=c
out=dict(fixtures=fixtures,structured_checked=count,canonical=can,first_obstructions=found,scope='four fixed one-parameter deformations, 8<=m<=180; no inference outside this domain')
(L/'exact-checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(dict(structured_checked=count,canonical=can,obstructions={k:dict(g=v['generators'],PF=v['PF'],rows=[{z:r[z] for z in ['f','reflection','factorizations','union_support']} for r in v['rows']]) for k,v in found.items()}),indent=2))
