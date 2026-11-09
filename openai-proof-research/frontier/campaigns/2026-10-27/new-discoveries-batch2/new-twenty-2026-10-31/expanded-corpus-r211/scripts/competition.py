import pathlib,itertools,json,sys,collections
import networkx as nx
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for n in range(3,int(sys.argv[1])+1):
 pairs=list(itertools.combinations(range(n),2));masks={};av=set()
 for p in itertools.permutations(range(n)):
  pre=[];lo=n
  for a in p:pre.append(lo);lo=min(lo,a)
  mask=sum(1<<k for k,(i,j) in enumerate(pairs) if pre[i]<min(p[i],p[j]));masks.setdefault(mask,p)
  # no increasing subsequence of length three
  low=n;second=n;avoids=True
  for a in p:
   if a>second:avoids=False;break
   if a>low:second=min(second,a)
   low=min(low,a)
  if avoids:av.add(mask)
 buckets=collections.defaultdict(list);count=0;clawfree=0;bad=[]
 # First classify avoiding graphs; then all clawfree graphs must match.
 def graph(m):
  g=nx.Graph();g.add_nodes_from(range(n));g.add_edges_from(e for k,e in enumerate(pairs) if m>>k&1);return g
 def key(g):return tuple(sorted(dict(g.degree()).values()))
 for m in av:
  g=graph(m);k=key(g)
  if not any(nx.is_isomorphic(g,h) for h in buckets[k]):buckets[k].append(g);count+=1
 for m,p in masks.items():
  g=graph(m)
  if any(all(not g.has_edge(a,b) for a,b in itertools.combinations(t,2)) for v in g for t in itertools.combinations(g[v],3)):continue
  clawfree+=1
  if not any(nx.is_isomorphic(g,h) for h in buckets[key(g)]):bad.append({'permutation':p,'edges':list(g.edges())})
 row={'n':n,'permutations':__import__('math').factorial(n),'distinct_labelled_graphs':len(masks),'avoiding_isomorphism_types':count,'clawfree_labelled_graphs':clawfree,'unmatched':bad};out.append(row);print(row,flush=True);(D/'outputs/competition.json').write_text(json.dumps(out,indent=2)+'\n')
