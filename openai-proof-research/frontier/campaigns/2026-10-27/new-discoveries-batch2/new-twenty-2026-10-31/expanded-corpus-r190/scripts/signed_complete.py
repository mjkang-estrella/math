import pathlib,json,itertools,random,time,networkx as nx
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(190);out=[]
def decomposition(n):
 # round-robin 1-factorization, pair matchings; union is cycles
 fs=[]
 for k in range(n-1):fs.append([(n-1,k)]+[((k+j)%(n-1),(k-j)%(n-1)) for j in range(1,n//2)])
 return fs[0],[fs[j]+fs[j+1] for j in range(1,n-1,2)]
def check(n,neg,perm):
 M,fs=decomposition(n)
 for f in fs:
  adj=[[] for _ in range(n)]
  for a,b in f:adj[a].append(b);adj[b].append(a)
  seen=set()
  for a in range(n):
   if a in seen:continue
   prev=-1;v=a;parity=0
   while v not in seen:
    seen.add(v);w=next(z for z in adj[v] if z!=prev);parity^=(tuple(sorted((perm[v],perm[w]))) in neg);prev,v=v,w
   if parity:return False
 return True
for g in nx.graph_atlas_g():
 if len(g)!=7:continue
 neg={tuple(sorted((a+1,b+1))) for a,b in g.edges()};n=8;found=None
 for perm in itertools.permutations(range(1,n)):
  p=(0,)+perm
  if check(n,neg,p):found=p;break
 out.append({'n':n,'negative_edges':sorted(neg),'permutation':found})
 if found is None:print('FAIL',out[-1],flush=True)
(D/'outputs/signed-complete-atlas.json').write_text(json.dumps(out));print('n8 atlas',len(out),'failures',sum(z['permutation'] is None for z in out),flush=True)
for n in [10,12,14,16]:
 rows=[]
 for j in range(200):
  prob=[.02,.1,.3,.5,.7,.9,.98][j%7];neg={(a,b) for a in range(1,n) for b in range(a+1,n) if rng.random()<prob};found=None
  for trial in range(2000):
   p=[0]+rng.sample(list(range(1,n)),n-1)
   if check(n,neg,p):found=p;break
  rows.append({'negative_edges':sorted(neg),'permutation':found,'trials':trial+1})
 (D/f'outputs/signed-complete-random-{n}.json').write_text(json.dumps(rows));print('random',n,'failed template searches',sum(z['permutation'] is None for z in rows),flush=True)
