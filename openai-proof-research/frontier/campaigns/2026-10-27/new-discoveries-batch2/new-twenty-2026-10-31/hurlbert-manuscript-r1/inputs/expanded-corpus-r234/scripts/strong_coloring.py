import random,itertools,json
rng=random.Random(356405)
def connected(n,ee,skip=None):
 seen={0}
 while True:
  more=seen|{b for j,(a,b) in enumerate(ee) if j!=skip and a in seen}|{a for j,(a,b) in enumerate(ee) if j!=skip and b in seen}
  if more==seen:return len(seen)==n
  seen=more
def solve(n,ee,k):
 m=len(ee);adj=[set() for _ in ee];neigh=[set() for _ in range(n)]
 for a,b in ee:neigh[a].add(b);neigh[b].add(a)
 for i,(a,b) in enumerate(ee):
  for j,(c,d) in enumerate(ee[:i]):
   if {a,b}&{c,d} or c in neigh[a] or c in neigh[b] or d in neigh[a] or d in neigh[b]:adj[i].add(j);adj[j].add(i)
 col=[-1]*m;nodes=0
 def rec(left,maxc):
  nonlocal nodes
  nodes+=1
  if nodes>50000:raise TimeoutError
  if not left:return True
  v=max((i for i in range(m) if col[i]<0),key=lambda i:(len({col[j] for j in adj[i] if col[j]>=0}),len(adj[i])))
  used={col[j] for j in adj[v]}
  for c in range(min(k,maxc+2)):
   if c in used:continue
   col[v]=c
   if rec(left-1,max(c,maxc)):return True
  col[v]=-1;return False
 try:return ('colorable' if rec(m,-1) else 'uncolorable'),nodes
 except TimeoutError:return 'node_cap',nodes
def girth5(n,ee):
 adj=[set() for _ in range(n)]
 for a,b in ee:adj[a].add(b);adj[b].add(a)
 for a,b in ee:
  if adj[a]&adj[b]:return False
 for a,b in itertools.combinations(range(n),2):
  if len(adj[a]&adj[b])>1:return False
 return True
for n in [14,16,18,20,24,30]:
 done=0;counts={};attempts=0
 while done<100 and attempts<100000:
  attempts+=1;stubs=list(range(n))*3;rng.shuffle(stubs);ee=[tuple(sorted(stubs[i:i+2])) for i in range(0,3*n,2)]
  if any(a==b for a,b in ee) or len(set(ee))<len(ee) or not connected(n,ee):continue
  done+=1;bridgeless=all(connected(n,ee,j) for j in range(len(ee)));g5=girth5(n,ee)
  for label,k,cond in [('a',9,bridgeless),('b',8,bridgeless),('c',7,g5)]:
   if cond:
    s,nodes=solve(n,ee,k);key=label+'_'+s;counts[key]=counts.get(key,0)+1
    if s=='uncolorable':print('POTENTIAL',n,label,ee,flush=True)
 print(json.dumps({'n':n,'simple_connected_cubic_samples':done,'counts':counts}),flush=True)
