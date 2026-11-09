import random,json,sys
random.seed(129)
def color(adj):
 c=[-1]*len(adj);calls=0
 def go(left):
  nonlocal calls
  calls+=1
  if calls>30000:return None
  if not left:return True
  u=max(left,key=lambda u:(len({c[v] for v in adj[u] if c[v]>=0}),len(adj[u])))
  used={c[v] for v in adj[u] if c[v]>=0}
  for x in range(min(3,max(c)+2)):
   if x not in used:
    c[u]=x;r=go(left-{u})
    if r is not False:return r
  c[u]=-1;return False
 return go(set(range(len(adj)))),calls
for n in range(19,41):
 good=unknown=0; maxcalls=0
 for trial in range(50):
  w=list(range(n)); wires=[[] for _ in w];word=[]
  while True:
   av=[i for i in range(n-1) if w[i]<w[i+1]]
   if not av:break
   j=random.choice(av);v=len(word);word.append(j)
   wires[w[j]].append(v);wires[w[j+1]].append(v);w[j],w[j+1]=w[j+1],w[j]
  adj=[set() for _ in word]
  for wire in wires:
   for a,b in zip(wire,wire[1:]+wire[:1]):adj[a].add(b);adj[b].add(a)
  r,c=color(adj);maxcalls=max(maxcalls,c)
  if r is False:
   print(json.dumps({'FAIL':True,'n':n,'trial':trial,'word':word,'adj':[sorted(x) for x in adj]}),flush=True);sys.exit()
  if r:good+=1
  else:unknown+=1
 print(json.dumps({'n':n,'sampled_reduced_words':50,'3colorable':good,'solver_unknown':unknown,'max_nodes':maxcalls}),flush=True)
