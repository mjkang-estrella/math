import pathlib,json,itertools,random,time,sys
D=pathlib.Path(__file__).resolve().parents[1]
def closure(n,edges):
 s=[0]*n
 for a,b in edges:s[a]|=1<<b
 for k in range(n):
  for i in range(n):
   if s[i]>>k&1:s[i]|=s[k]
 return s

def feasible(s,limit=100000):
 n=len(s);labels=[-1]*n;calls=0
 def key(v):return tuple(sorted(labels[u] for u in range(n) if s[v]>>u&1))+(n,)*n
 def valid(order):
  sk=[sum(1<<(n-1-labels[u]) for u in range(n) if s[v]>>u&1) for v in order]
  ak=[sum(1<<(n-1-labels[u]) for u in range(n) if s[u]>>v&1) for v in order]
  return all(sk[i]>sk[i+1] or sk[i]==sk[i+1] and ak[i]>=ak[i+1] for i in range(n-1))
 def rec(rem):
  nonlocal calls
  calls+=1
  if calls>limit:raise TimeoutError
  if not rem:return tuple(sorted(range(n),key=lambda v:labels[v])) if valid(sorted(range(n),key=lambda v:labels[v])) else None
  sinks=[v for v in rem if not any(s[v]>>u&1 for u in rem)]
  keys={v:key(v) for v in sinks};best=max(keys.values());choices=[v for v in sinks if keys[v]==best]
  for v in choices:
   labels[v]=len(rem)-1;r=rec(rem-{v})
   if r is not None:return r
   labels[v]=-1
  return None
 try:r=rec(set(range(n)));return r,calls,False
 except TimeoutError:return None,calls,True
rng=random.Random(195);out=[]
for n in range(8,17):
 hist={'n':n,'trials':0,'feasible':0,'limited':0,'nodes':0};t=time.monotonic()
 for trial in range(150):
  prob=[.12,.25,.4,.6,.8][trial%5]
  # backbone ensures weak connectivity, plus random forward arcs
  e={(i,rng.randrange(i+1,n)) for i in range(n-1)}
  e|={(i,j) for i in range(n) for j in range(i+1,n) if rng.random()<prob}
  s=closure(n,e);r,c,limited=feasible(s,20000);hist['trials']+=1;hist['nodes']+=c
  if r is not None:hist['feasible']+=1
  elif limited:hist['limited']+=1
  else:
   hist['potential_failure']={'edges':sorted(e),'successors':s};break
 hist['seconds']=time.monotonic()-t;out.append(hist);print(hist,flush=True)
 if 'potential_failure'in hist:break
(D/'outputs/dag.json').write_text(json.dumps(out,indent=2))
