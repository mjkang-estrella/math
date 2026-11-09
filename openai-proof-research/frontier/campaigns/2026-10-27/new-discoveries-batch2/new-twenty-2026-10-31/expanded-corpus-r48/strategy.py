from pathlib import Path
import networkx as nx,functools,json,resource,os,time
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(80,80));os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
p=Path(__file__).parent; start=time.time();rows=[];bad=[]
G=nx.Graph([(0,1),(0,5),(1,2),(1,6),(2,3),(3,4),(4,5),(5,6)])
for G in [G]:
 n=len(G)
 if n<1:continue
 delta=min(dict(G.degree()).values())
 if delta<2:continue
 full=(1<<n)-1;N=[sum(1<<u for u in [v,*G[v]]) for v in G]
 @functools.lru_cache(None)
 def f(s,d,st):
  if any(s&z==z for z in N):return s.bit_count()
  if all(d&z for z in N):return n+1
  rem=full^(s|d)
  if not rem:return n+1
  vals=[f(s|1<<v,d,False) if st else f(s,d|1<<v,True) for v in range(n) if rem>>v&1]
  return min(vals) if st else max(vals)
 a=f(0,0,True);b=f(0,0,False);row={'n':n,'delta':delta,'edges':list(G.edges()),'S':a if a<=n else None,'D':b if b<=n else None,'Sbound':(n+1)//2-delta+1,'Dbound':n//2-delta+1};rows.append(row)
 if a<=n and a>row['Sbound'] or b<=n and b>row['Dbound']:bad.append(row)
 print('initial',f(0,0,True))
 def tree(s,d,st,depth=0):
  if any(s&z==z for z in N):return {'win':s}
  rem=full^(s|d)
  if not rem:return {'loss':True}
  moves=[v for v in range(n) if rem>>v&1]
  if st:
   v=min(moves,key=lambda v:f(s|1<<v,d,False));return {'S':v,'next':tree(s|1<<v,d,False,depth+1)}
  return {'D':{v:tree(s,d|1<<v,True,depth+1) for v in moves}}
 print(json.dumps(tree(0,0,True),indent=2))
