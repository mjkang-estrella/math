import itertools,json
n=4
ps=list(itertools.permutations(range(n)))
def red(p):return tuple(sorted(p).index(x) for x in p)
es=[(red(p[:-1]),red(p[1:])) for p in ps];out={}
for i,(a,b) in enumerate(es):out.setdefault(a,[]).append(i)
checked=bad=0;limit=100000

def check(t):
 adj=[set() for _ in range(24)]
 for i,e in enumerate(t):
  p=ps[e]
  for a in range(4):
   for b in range(4):
    if p[a]<p[b]:adj[(i+a)%24].add((i+b)%24)
 deg=[0]*24
 for row in adj:
  for j in row:deg[j]+=1
 stack=[i for i in range(24) if not deg[i]];count=0
 while stack:
  i=stack.pop();count+=1
  for j in adj[i]:
   deg[j]-=1
   if not deg[j]:stack.append(j)
 return count==24

def rec(t,used,v):
 global checked,bad
 if checked>=limit:return
 if len(t)==24:
  if v!=es[0][0]:return
  checked+=1
  if not check(t):
   bad+=1
   if bad==1:print('first_bad',t,flush=True)
  return
 for e in out[v]:
  if not used>>e&1:rec(t+[e],used|1<<e,es[e][1])
rec([0],1,es[0][1]);print(json.dumps({'n':4,'fixed_first':'1234','completed':checked,'nonrealizable':bad,'cap':limit,'exhaustive':checked<limit}),flush=True)
