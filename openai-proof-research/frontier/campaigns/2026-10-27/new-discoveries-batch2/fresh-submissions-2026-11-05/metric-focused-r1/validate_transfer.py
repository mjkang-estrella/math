import collections,json,random,resource
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(90,90));resource.setrlimit(resource.RLIMIT_AS,(700*1024**2,700*1024**2))
p=Path(__file__).parent;graphs=json.loads((p/'search-input.json').read_text());rng=random.Random(381600)
def counts(g,r=None):
 n=g['n'];a=[set() for _ in range(n)]
 for u,v in g['edges']:a[u].add(v);a[v].add(u)
 C=collections.Counter()
 for mask in range(1<<n):
  S={v for v in range(n) if mask>>v&1};W=set(range(n))-S;e=sum(u in S and v in S for u,v in g['edges']);q=sum((u in S)!=(v in S) for u,v in g['edges']);todo=set(S);c=0
  while todo:
   c+=1;front={todo.pop()}
   while front:
    new=set().union(*(a[v] for v in front))&todo;todo-=new;front=new
  z=sum(not(a[v]&S) for v in W)
  if r is None:key=(len(S),e,c,q,z)
  else:
   b=int(r in S);d=int(not b and bool(a[r]&S));key=(len(S),e,c,q,z-int(not b and not d),b,d)
  C[key]+=1
 return C
# Identify roots 0, graph vertex labels generated consecutively.
checks=0;subset_pairs=0
small=[g for g in graphs if g['n']<=5]
for _ in range(100):
 A=rng.choice(small);B=rng.choice(small);ra=rng.randrange(A['n']);rb=rng.randrange(B['n']);ca=counts(A,ra);cb=counts(B,rb);pred=collections.Counter()
 for (ka,ea,cc,qa,za,b,da),va in ca.items():
  for (kb,eb,cd,qb,zb,bb,db),vb in cb.items():
   if b==bb:pred[(ka+kb-b,ea+eb,cc+cd-b,qa+qb,za+zb+int(not b and not da and not db))]+=va*vb
 mpA={ra:0};mpB={rb:0};nextv=1
 for mp,G in [(mpA,A),(mpB,B)]:
  for v in range(G['n']):
   if v not in mp:mp[v]=nextv;nextv+=1
 G=dict(n=nextv,edges=[[mp[u],mp[v]] for H,mp in [(A,mpA),(B,mpB)] for u,v in H['edges']]);assert pred==counts(G);checks+=1;subset_pairs+=1<<G['n']
# Cross-language exact packed signature checks; JS emits probes separately.
probes=json.loads((p/'signature-probes.json').read_text());cross=0
for pr in probes:
 C=counts(graphs[pr['id']],pr['root']);encoded=[]
 for key,mult in C.items():
  v=key[0]
  for x in key[1:]:v=v*64+x
  encoded.extend([v]*mult)
 assert sorted(encoded)==pr['values'];cross+=len(encoded)
res=dict(coalescence_pairs=checks,total_coalesced_subsets=subset_pairs,cross_language_subsets=cross,probe_graphs=len(probes),failures=0,seed=381600);(p/'transfer-validation.json').write_text(json.dumps(res,indent=2));print(res)
