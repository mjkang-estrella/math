from functools import lru_cache
from itertools import combinations
import pathlib,json,time
D=pathlib.Path(__file__).resolve().parents[1]
def comps(n,t):
 if n==1:yield(t,);return
 for a in range(t+1):
  for x in comps(n-1,t-a):yield(a,)+x
out=[];viol=[];start=time.monotonic()
for n in range(2,6):
 edges=list(combinations(range(n),2))
 for mask in range(1,1<<len(edges)):
  adj=[[] for _ in range(n)]
  for b,(u,v) in enumerate(edges):
   if mask>>b&1:adj[u].append(v);adj[v].append(u)
  seen={0}
  for _ in range(n):seen|={v for u in list(seen) for v in adj[u]}
  if len(seen)!=n:continue
  # order5 restrict to diameter2 and deterministic sample; order<=4 all labeled connected graphs
  if n==5:
   if mask%7:continue
   if any(len(set([u]+adj[u]+[w for v in adj[u] for w in adj[v]]))<n for u in range(n)):continue
  targets=list(comps(n,2));single=[tuple(2 if i==v else 0 for i in range(n)) for v in range(n)]
  worst={d:0 for d in targets};resolved=set();configcount=0
  @lru_cache(None)
  def solve(c,d):
   if all(x>=y for x,y in zip(c,d)):return True
   for u in range(n):
    if c[u]>=2:
     for v in adj[u]:
      q=list(c);q[u]-=2;q[v]+=1
      if solve(tuple(q),d):return True
   return False
  for total in range(2,18):
   active=[d for d in targets if d not in resolved]
   if not active:break
   fails=set()
   for c in comps(n,total):
    configcount+=1
    for d in active:
     if not solve(c,d):fails.add(d);worst[d]=total
   resolved.update(d for d in active if d not in fails)
   if time.monotonic()-start>105:break
  pit=max(worst[d]+1 for d in single)
  bad=[(d,worst[d]+1) for d in targets if d in resolved and all(s in resolved for s in single) and worst[d]+1>pit]
  if bad:viol.append({'n':n,'graph_mask':mask,'pi2':pit,'bad':bad})
  out.append({'n':n,'graph_mask':mask,'pi2':pit,'max_target':max(worst.values())+1,'all_resolved':len(resolved)==len(targets),'configurations':configcount,'cache_states':solve.cache_info().currsize})
  solve.cache_clear()
  if time.monotonic()-start>105:break
 if time.monotonic()-start>105:break
r={'graphs':out,'violations':viol,'seconds':time.monotonic()-start,'scope':'all connected labeled simple graphs n2..4; n5 diameter<=2 with edge mask divisible by7, subject to105s internal stop; demand total2; exact decreasing-total recursion; totals2..17','complete_through_order4':n>=5}
(D/'outputs/pebbling-search.json').write_text(json.dumps(r,indent=2));print({k:v for k,v in r.items() if k!='graphs'});print('graphs',len(out),'configurations',sum(x['configurations'] for x in out))
