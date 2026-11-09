import itertools,json,time
for dims in [(3,),(5,),(7,),(9,),(3,3),(11,),(13,),(15,),(17,),(19,),(21,),(3,9),(27,),(3,3,3),(3,15),(45,)]:
 elements=list(itertools.product(*(range(d) for d in dims)));idx={x:i for i,x in enumerate(elements)};N=len(elements)
 def op(a,b,sgn=1):return idx[tuple((x+sgn*y)%d for x,y,d in zip(elements[a],elements[b],dims))]
 pairs=[[] for _ in elements]
 for x in range(1,N):
  for y in range(x+1,N):
   d=op(x,y,-1);s=op(x,y);nd=op(0,d,-1)
   if s and d!=nd:
    entry=(x,y,(1<<x)|(1<<y),(1<<d)|(1<<nd),1<<s);pairs[x].append(entry);pairs[y].append(entry)
 nodes=0;t0=time.monotonic();budget=2_000_000
 def solve(rem,diffs,sums,ans):
  global nodes
  nodes+=1
  if nodes>budget:return None
  if not rem:return ans
  best=None
  for x in range(1,N):
   if rem>>x&1:
    choices=[p for p in pairs[x] if p[2]&rem==p[2] and not(p[3]&diffs or p[4]&sums)]
    if not choices:return None
    if best is None or len(choices)<len(best):best=choices
  for x,y,mask,d,s in best:
   z=solve(rem^mask,diffs|d,sums|s,ans+[(x,y)])
   if z is not None:return z
  return None
 ans=solve((1<<N)-2,0,0,[])
 if ans is not None:
  assert len(set(itertools.chain.from_iterable(ans)))==N-1
  assert len({op(x,y) for x,y in ans})==(N-1)//2
  assert len({op(x,y,-1) for x,y in ans}|{op(y,x,-1) for x,y in ans})==N-1
 print(json.dumps({'group':dims,'order':N,'nodes':nodes,'status':'starter_found' if ans is not None else ('budget_inconclusive' if nodes>budget else 'exhaustive_nonexistence'),'pairs':ans,'seconds':time.monotonic()-t0}),flush=True)
