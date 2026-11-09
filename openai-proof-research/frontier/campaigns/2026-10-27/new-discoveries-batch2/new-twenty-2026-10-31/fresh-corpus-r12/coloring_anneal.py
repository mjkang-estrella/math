import random,math,json,time
from pathlib import Path
random.seed(332204);n=12;k=7

def score(a):
 v=a[:n];e=a[n:]
 bad=sum(v[i]==v[(i+1)%n] for i in range(n))+sum(e[i] in [v[i],v[(i+1)%n]] for i in range(n))+sum(e[i]==e[(i+1)%n] for i in range(n))
 ps=[[frozenset([e[i-1],e[i]]) for i in range(n)],[frozenset([v[i-1],v[i],v[(i+1)%n]]) for i in range(n)],[frozenset([e[i-1],e[i],v[i]]) for i in range(n)],[frozenset([e[i-1],e[i],v[i-1],v[i],v[(i+1)%n]]) for i in range(n)]]
 return 5*bad+sum(n-len(set(p)) for p in ps),ps
start=time.monotonic();best=1000
for restart in range(25):
 a=[random.randrange(k) for _ in range(2*n)];s,_=score(a)
 for step in range(12000):
  ix=random.randrange(2*n);old=a[ix];a[ix]=random.randrange(k);t,ps=score(a)
  temp=0.12+1.8*(1-step/12000)**2
  if t<=s or random.random()<math.exp((s-t)/temp):s=t
  else:a[ix]=old
  best=min(best,s)
  if s==0:
   row={'n':n,'k':k,'vertex_colors':a[:n],'edge_colors':a[n:],'palettes':[[sorted(x) for x in p] for p in ps],'seconds':time.monotonic()-start,'restart':restart,'step':step,'status':'exact finite validation after heuristic search; no novelty claim'}
   Path(__file__).with_name('coloring-diagnostics.json').write_text(json.dumps(row,indent=2)+'\n');print(row);raise SystemExit
print('No witness; best penalty',best)
