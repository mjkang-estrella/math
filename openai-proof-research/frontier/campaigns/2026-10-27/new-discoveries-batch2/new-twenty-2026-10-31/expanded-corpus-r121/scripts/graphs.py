import itertools,json,random,time
# Exact DSATUR on squared line graph.
def test(n,E):
 adj=[set() for _ in range(n)]
 for a,b in E:adj[a].add(b);adj[b].add(a)
 if any(len(a)>3 for a in adj):return None
 def connected(skip=None):
  seen={0};todo=[0]
  while todo:
   a=todo.pop()
   for b in adj[a]:
    if skip and {a,b}==set(skip):continue
    if b not in seen:seen.add(b);todo.append(b)
  return len(seen)==n
 if not connected() or any(not connected(e) for e in E):return None
 m=len(E);A=[set() for _ in E]
 for i,(a,b) in enumerate(E):
  for j,(c,d) in enumerate(E[:i]):
   if len({a,b,c,d})<4 or any(x in adj[y] for x in (a,b) for y in (c,d)):A[i].add(j);A[j].add(i)
 col=[-1]*m
 def rec(left,used):
  if not left:return True
  v=max(left,key=lambda x:(len({col[j] for j in A[x] if col[j]>=0}),len(A[x])))
  ban={col[j] for j in A[v]};new=left-{v}
  for c in range(min(used+1,9)):
   if c not in ban:
    col[v]=c
    if rec(new,max(used,c+1)):return True
  col[v]=-1;return False
 return rec(set(range(m)),0)
for n in range(3,7):
 pairs=list(itertools.combinations(range(n),2));valid=bad=0
 for mask in range(1<<len(pairs)):
  E=[e for i,e in enumerate(pairs) if mask>>i&1];r=test(n,E)
  if r is not None:
   valid+=1
   if not r:bad+=1;print('FAIL',n,E,flush=True)
 print(json.dumps(dict(mode='all_labeled_connected_bridgeless_subcubic',n=n,all_graphs=1<<len(pairs),eligible=valid,failures=bad)),flush=True)
rng=random.Random(121)
for n in [14,16,18,20,24,30]:
 valid=bad=0
 for it in range(3000):
  stubs=list(range(n))*3;rng.shuffle(stubs);E=[tuple(sorted(stubs[i:i+2])) for i in range(0,3*n,2)]
  if any(a==b for a,b in E) or len(set(E))!=len(E):continue
  r=test(n,E)
  if r is None:continue
  valid+=1
  if not r:bad+=1;print('FAIL',n,E,flush=True)
 print(json.dumps(dict(mode='configuration_sample',n=n,attempts=3000,eligible=valid,failures=bad)),flush=True)
