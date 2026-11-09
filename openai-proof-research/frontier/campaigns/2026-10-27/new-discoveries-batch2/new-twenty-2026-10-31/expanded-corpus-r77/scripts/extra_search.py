import sys,itertools as it,pathlib,json,math
from fractions import Fraction as F
D=pathlib.Path(__file__).resolve().parents[1]
def save(k,x):(D/f'outputs/search-{k}.json').write_text(json.dumps(x,indent=2)+'\n');print(x)
def trees():
 rows=[]
 for n in range(2,7):
  cnt=0
  for word in it.product(range(n),repeat=n-2):
   deg=[1+word.count(v) for v in range(n)];es=[]
   for v in word:
    u=next(i for i in range(n) if deg[i]==1);es.append((u,v));deg[u]-=1;deg[v]-=1
   es.append(tuple(i for i in range(n) if deg[i]==1));cnt+=1
   assert any(len({abs(p[u]-p[v]) for u,v in es})==n-1 for p in it.permutations(range(n)))
  rows.append([n,cnt])
 save('trees',dict(id=315999,space='all Prufer words for labeled trees orders2..6, all vertex bijections until first graceful labeling',rows=rows))
def woodall():
 rows=[]
 for n in range(2,5):
  es=list(it.permutations(range(n),2));app=0;counts={}
  for mask in range(1<<len(es)):
   edges=[e for j,e in enumerate(es) if mask>>j&1];cuts=[]
   for S in range(1,(1<<n)-1):
    if not any(not(S>>u&1) and S>>v&1 for u,v in edges):cuts.append([j for j,(u,v) in enumerate(edges) if S>>u&1 and not(S>>v&1)])
   if not cuts:continue
   k=min(map(len,cuts));counts[k]=counts.get(k,0)+1
   if k<2:continue
   app+=1
   assert any(all(len({c[j] for j in cut})==k for cut in cuts) for c in it.product(range(k),repeat=len(edges)))
  rows.append(dict(n=n,digraphs=1<<len(es),cut_minimum_counts=counts,nontrivial_color_tests=app))
 save('woodall',dict(id=316037,space='all loopless simple digraphs on2..4 vertices including opposite arcs; k=0 and k=1 trivial; exact k-color dicut hitting condition',rows=rows))
def harbourne():
 rows=[]
 for p in [2,3]:
  pts=[a for a in it.product(range(p),repeat=3) if any(a) and next(x for x in a if x)==1]
  inc=[sum(1<<j for j,x in enumerate(pts) if sum(a*b for a,b in zip(l,x))%p==0) for l in pts];best={}
  for mask in range(1,1<<len(pts)):
   d=mask.bit_count()
   if d<2:continue
   ms=[sum((mask>>j&1) and (inc[j]>>h&1) for j in range(len(pts))) for h in range(len(pts))];ms=[m for m in ms if m>=2];v=F(d*d-sum(m*m for m in ms),len(ms))
   if d not in best or v<best[d]:best[d]=v
  rows.append(dict(p=p,lines=len(pts),subsets=(1<<len(pts))-1,minima={str(d):str(v) for d,v in best.items()}))
 save('harbourne',dict(id=400138,space='all subsets of lines in PG(2,2) and PG(2,3); no all-field lower bound',rows=rows))
def gaudin():
 import sympy as s
 l,m=s.symbols('l m');rows=[]
 for k in range(11):
  c=s.symbols('c1:'+str(k+1));polys=[]
  for i in range(k+1):
   z=0
   for a in it.product(*(range(i//j+1) for j in range(1,i+1))):
    if sum((j+1)*v for j,v in enumerate(a))==i:z+=s.prod(c[j]**v/s.factorial(v) for j,v in enumerate(a))*l**sum(a)
   polys.append(z)
  assert s.expand(sum(polys[i]*polys[k-i].subs(l,m) for i in range(k+1))-polys[k].subs(l,l+m))==0;rows.append(k)
 save('gaudin',dict(id=380929,space='symbolic identity all coefficients, degrees0..10',degrees=rows))
if __name__=='__main__':globals()[sys.argv[1]]()
