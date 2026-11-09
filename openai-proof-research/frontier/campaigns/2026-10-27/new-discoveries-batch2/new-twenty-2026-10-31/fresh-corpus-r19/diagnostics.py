import itertools, random, json, pathlib, time, resource, os, functools
os.sched_setaffinity(0,{0,1})
resource.setrlimit(resource.RLIMIT_CPU,(80,80))
resource.setrlimit(resource.RLIMIT_AS,(1800*1024**2,1800*1024**2))
out=pathlib.Path(__file__).parent
start=time.monotonic()
# Exact odd-graph adjacency, with randomized greedy independent domination.
n,m=15,7
vertices=[sum(1<<i for i in c) for c in itertools.combinations(range(n),m)]
index={v:i for i,v in enumerate(vertices)}
adj=[]
for v in vertices:
 c=((1<<n)-1)^v
 adj.append([index[c^(1<<j)] for j in range(n) if c>>j&1])
rng=random.Random(1901); trials=[]; best=None
for trial in range(100):
 order=list(range(len(vertices)));rng.shuffle(order);blocked=set();chosen=[]
 for i in order:
  if i not in blocked:
   chosen.append(i);blocked.add(i);blocked.update(adj[i])
 assert len(blocked)==len(vertices)
 assert all(not(set(adj[i])&set(chosen)) for i in chosen)
 trials.append(len(chosen))
 if best is None or len(chosen)<len(best):best=chosen
(out/'bicommutative-search.json').write_text(json.dumps({'n':n,'m':m,'source_size':1870,'trials':trials,'best_size':len(best),'best_masks':[vertices[i] for i in best],'method':'random-order greedy maximal independent set; exact verification','seconds':time.monotonic()-start},indent=2)+'\n')
print('bicommutative',min(trials),max(trials),flush=True)
# Source legal-play recurrence: W maximizes own candies over winning moves;
# L minimizes W. This is exact exploratory Python, not a Lean endpoint.
@functools.lru_cache(None)
def w(g):
 if not g:return 0
 xor=functools.reduce(int.__xor__,g,0)
 if xor:
  return max(a-(a^xor)+w(tuple(sorted(g[:i]+g[i+1:]+((a^xor,) if a^xor else ())))) for i,a in enumerate(g) if a^xor<a)
 return min(w(tuple(sorted(g[:i]+g[i+1:]+((b,) if b else ())))) for i,a in enumerate(g) for b in range(a))
def bitpart(a):
 bits=[1<<i for i in range(a.bit_length()) if a>>i&1]
 def rec(i,blocks):
  if i==len(bits):
   if len(blocks)>1:yield tuple(sorted(blocks))
   return
  for j in range(len(blocks)):
   z=blocks.copy();z[j]+=bits[i];yield from rec(i+1,z)
  yield from rec(i+1,blocks+[bits[i]])
 yield from rec(0,[])
records=[]
for a in range(3,24):
 if a.bit_count()<2:continue
 for b in range(a+1,42):
  c=a^b
  if c<=b:continue
  g=(a,b,c); wg=w(g); splits=sorted(set(bitpart(a)))
  vals=[{'split':s,'W':w(tuple(sorted(s+(b,c))))} for s in splits]
  r={'G':g,'W':wg,'V':sum(g)-2*wg,'splits':vals,'counterexample':all(z['W']>wg for z in vals)}
  records.append(r)
  print(json.dumps(r),flush=True)
  (out/'candy-search.json').write_text(json.dumps({'records':records,'memo':str(w.cache_info()),'seconds':time.monotonic()-start},indent=2)+'\n')
  if time.monotonic()-start>65:raise SystemExit(0)
