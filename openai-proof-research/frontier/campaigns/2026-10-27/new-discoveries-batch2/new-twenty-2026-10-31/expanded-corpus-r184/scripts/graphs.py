import pathlib,itertools,json,random,sys
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(184)
def rainbow(edges,used=0):
 if not edges:return True
 opts=[[(1<<a)|(1<<b) for a,b in e if not used&((1<<a)|(1<<b))] for e in edges]
 j=min(range(len(opts)),key=lambda j:len(opts[j]))
 return any(rainbow(edges[:j]+edges[j+1:],used|e) for e in opts[j])
if sys.argv[1]=='rainbow':
 out=[]
 for n in range(2,13):
  count=0
  for trial in range(500):
   v=2*(n+2)+rng.randrange(5);edges=[]
   for c in range(n):
    p=rng.sample(range(v),2*(n+2));edges.append(list(zip(p[::2],p[1::2])))
   assert rainbow(edges),(n,edges);count+=1
  out.append({'colors':n,'class_size':n+2,'samples':count,'vertices':'2(n+2)+0..4','violations':0})
 (D/'outputs/rainbow-results.json').write_text(json.dumps(out,indent=2));print(out)
elif sys.argv[1]=='cycles':
 # All 2-regular missing-edge patterns at n=6, up to one matching normalized to identity.
 # Every such complement is a union of two perfect matchings.
 out=[];n=6
 for p in itertools.permutations(range(n)):
  if any(p[i]==i for i in range(n)):continue
  adj=[[j for j in range(n) if j not in [i,p[i]]] for i in range(n)]
  # enumerate every simple cycle, keeping its vertex mask and X-count
  graph=[set(x+n for x in a) for a in adj]+[set(i for i in range(n) if j in adj[i]) for j in range(n)]
  cycles=set()
  def dfs(start,path,mask):
   v=path[-1]
   if len(path)>=4 and start in graph[v]:cycles.add((mask,sum(x<n for x in path)))
   for w in graph[v]:
    if w>start and not mask>>w&1:dfs(start,path+[w],mask|1<<w)
  for a in range(n):dfs(a,[a],1<<a)
  ok={}
  for size in [2,3]:
   aa=[m for m,k in cycles if k==size];bb=[m for m,k in cycles if k==n-size]
   ok[size]=any(not a&b for a in aa for b in bb)
  assert all(ok.values()),(p,ok)
  out.append({'missing_second_matching':p,'cycle_masks':len(cycles),'partition_2_4':ok[2],'partition_3_3':ok[3]})
 (D/'outputs/cycles-results.json').write_text(json.dumps(out,indent=2));print('all',len(out),'normalized complement patterns passed')
