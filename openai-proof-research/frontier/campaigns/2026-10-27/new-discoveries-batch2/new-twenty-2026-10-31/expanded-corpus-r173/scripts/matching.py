import pathlib,itertools,functools,json,sys,time
D=pathlib.Path(__file__).resolve().parents[1];n=int(sys.argv[1]);start=time.time()
def match(v):
 if not v:yield ();return
 a=v[0]
 for b in v[1:]:
  for m in match([x for x in v if x not in (a,b)]):yield tuple(sorted(((a,b),)+m))
ms=list(match(list(range(n))));ix={m:i for i,m in enumerate(ms)};reach=[]
for m in ms:
 seen={m};todo=[m]
 while todo:
  x=todo.pop()
  for e,f in itertools.combinations(x,2):
   a,b,c,d=sorted(e+f);pairs=[((a,b),(c,d)),((a,c),(b,d)),((a,d),(b,c))];z=pairs.index(tuple(sorted((e,f))))
   for q in pairs[z+1:]:
    y=tuple(sorted(tuple(h for h in x if h not in (e,f))+q))
    if y not in seen:seen.add(y);todo.append(y)
 reach.append({ix[x] for x in seen})
seqs=[x for x in itertools.combinations_with_replacement(range(1,n),n) if sum(x)%2==0];seqs=[x[::-1] for x in seqs]
# Prescribed matching removed: residual graph forbidden to use those matching edges.
real=[set() for m in ms]
for j,m in enumerate(ms):
 forbidden=[0]*n
 for a,b in m:forbidden[a]|=1<<b;forbidden[b]|=1<<a
 @functools.lru_cache(None)
 def feasible(ds):
  if not any(ds):return True
  a=max(range(n),key=lambda i:ds[i]);d=ds[a];cand=[i for i in range(n) if i!=a and ds[i]>0 and not (forbidden[a]>>i&1)]
  if len(cand)<d:return False
  cand.sort(key=lambda i:-ds[i])
  for sub in itertools.combinations(cand,d):
   r=list(ds);r[a]=0
   for i in sub:r[i]-=1
   if feasible(tuple(r)):return True
  return False
 for k,s in enumerate(seqs):
  if feasible(tuple(d-1 for d in s)):real[j].add(k)
 print('matching',j,'of',len(ms),'sequences',len(real[j]),'cache',feasible.cache_info(),flush=True)
 feasible.cache_clear()
viol=[];comparable=0
for j in range(len(ms)):
 for i in range(len(ms)):
  if real[j]<=real[i]:
   comparable+=1
   if i not in reach[j]:viol.append({'lower':ms[i],'upper':ms[j]})
r={'n':n,'matchings':len(ms),'positive_sorted_even_degree_sequences':len(seqs),'preorder_pairs':comparable,'violations':viol,'wall':time.time()-start,'method':'exhaustive degree sequences; exact recursive f-factor feasibility; directed-switch transitive closure'}
(D/f'outputs/matching-{n}.json').write_text(json.dumps(r,indent=2));print(r)
