"""Finite exact diagnostics, not a proof or formal gate. Writes only stdout."""
from itertools import combinations,permutations
from fractions import Fraction as F
import random,json

def check(n,facets,trials):
 edges=sorted(set(e for t in facets for e in combinations(t,2)));m=len(edges)
 tri=sorted(set(t for a in facets for t in combinations(a,3)))
 ds=[sum(1<<j for j,t in enumerate(tri) if set(e)<=set(t)) for e in edges]
 delta=lambda x: xor(ds[i] for i in range(m) if x>>i&1)
 cut=lambda a:sum(1<<i for i,(u,v) in enumerate(edges) if ((a>>u)^(a>>v))&1)
 cuts={cut(a):a for a in range(1<<(n-1))}
 w0=[F(sum(v in t for t in facets),len(facets)*len(facets[0])) for v in range(n)]
 w1=[F(sum(set(e)<=set(t) for t in facets),len(facets)*len(list(combinations(facets[0],2)))) for e in edges]
 w2=[F(sum(set(t)<=set(a) for a in facets),len(facets)*len(list(combinations(facets[0],3)))) for t in tri]
 norm=lambda x,w:sum((v for i,v in enumerate(w) if x>>i&1),F(0))
 reps={}
 for x in range(1<<m):reps.setdefault(delta(x),x)
 assert len(reps)*len(cuts)==1<<m
 assert sum(norm(b,w2) for b in ds)==3
 alpha=min(norm(cut(a),w1)/min(norm(a,w0),1-norm(a,w0)) for a in range(1,(1<<n)-1))
 dist=[[n for _ in range(n)] for _ in range(n)]
 for i in range(n):dist[i][i]=0
 for u,v in edges:dist[u][v]=dist[v][u]=1
 for k in range(n):
  for i in range(n):
   for j in range(n):dist[i][j]=min(dist[i][j],dist[i][k]+dist[k][j])
 md=sum(w0[u]*w0[v]*dist[u][v] for u in range(n) for v in range(n))
 lower=alpha*md/2-1
 rng=random.Random(143+n);checked=0;min_gap=None
 for _ in range(trials):
  s={b:x^rng.choice(list(cuts)) for b,x in reps.items()}
  pots=[cuts[x^s[delta(x)]] for x in range(1<<m)]
  total=sum((norm(s[b]^s[b^ds[e]],w1) for b in reps for e in range(m)),F(0))/len(reps)
  assert total>=lower
  min_gap=total-lower if min_gap is None else min(min_gap,total-lower)
  for u,v in combinations(range(n),2):
   signs=[1-2*(((a>>u)^(a>>v))&1) for a in pots]
   co=signs[:];h=1
   while h<len(co):
    for i in range(0,len(co),2*h):
     for j in range(i,i+h): a,b=co[j],co[j+h];co[j],co[j+h]=a+b,a-b
    h*=2
   influence=sum(sum(signs[x]!=signs[x^(1<<e)] for x in range(1<<m)) for e in range(m))
   assert influence*(1<<m)==sum(a.bit_count()*c*c for a,c in enumerate(co))
   assert influence>=dist[u][v]*(1<<m)
   for a,c in enumerate(co):
    if c:
     boundary=xor((1<<edges[e][0])^(1<<edges[e][1]) for e in range(m) if a>>e&1)
     assert boundary==(1<<u)^(1<<v)
   checked+=1
 # Exact upper construction, including nonuniform incidence weights.
 aut=[];fs=set(facets)
 for perm in permutations(range(n)):
  if {tuple(sorted(perm[v] for v in t)) for t in facets}==fs:
   emap=[edges.index(tuple(sorted((perm[u],perm[v])))) for u,v in edges]
   aut.append(emap)
 def act(x,emap):return sum(1<<emap[i] for i in range(m) if x>>i&1)
 orbit=[set(a[e] for a in aut) for e in range(m)]
 gamma=min(sum(w1[i] for i in z) for z in orbit)
 parent={0:None};queue=[0];te=[]
 for u in queue:
  for i,(a,b) in enumerate(edges):
   if u not in (a,b):continue
   v=b if a==u else a
   if v not in parent:parent[v]=(u,i);queue.append(v);te.append(i)
 tm=sum(1<<i for i in te)
 sec={b:next(x^c for c in cuts if not ((x^c)&tm)) for b,x in reps.items()}
 assert all(delta(x)==b for b,x in sec.items())
 cycles=[sum(1 for e in range(m) if sec[ds[e]]>>f&1) for f in range(m)]
 lhs=sum(norm(sec[ds[e]],w1) for e in range(m))
 assert lhs==sum(w1[f]*cycles[f] for f in range(m))
 limit=2*max(max(row) for row in dist)+1
 assert lhs<=limit
 lam={b:min(norm(x^c,w1) for c in cuts) for b,x in reps.items()}
 for b,x in reps.items():
  total=F(0)
  for a in aut:
   inv=[a.index(i) for i in range(m)]
   y=act(sec[delta(act(x,inv))],a)
   assert delta(y)==b
   total+=norm(y,w1)
  assert total/len(aut)<=F(limit)/gamma*lam[b]
 return {'automorphisms':len(aut),'gamma':str(gamma),'upper_input_checks':len(reps),'vertices':n,'edges':m,'syndromes':len(reps),'sections':trials,'pair_Fourier_checks':checked,'alpha':str(alpha),'mean_distance':str(md),'minimum_inequality_slack':str(min_gap)}

def xor(a):
 r=0
 for x in a:r^=x
 return r
if __name__=='__main__':
 out=[check(4,[tuple(range(4))],12),check(5,[(0,1,2,3),(0,1,2,4)],4),check(6,[tuple(sorted((a,b,c))) for a in [0,1] for b in [2,3] for c in [4,5]],3)]
 print(json.dumps({'diagnostics_only':True,'cases':out},indent=2))
