import itertools,collections,time,json,sys
T=time.monotonic();total=0

def check(v,k,bb,e):
 blocks=set()
 for j in range(e):
  for b in bb:
   for singles in itertools.product(range(v),repeat=e-1):
    others=iter(singles); blocks.add(sum(1<<(j*v+x) for x in b)|sum(1<<(l*v+next(others)) for l in range(e) if l!=j))
 n=v*e; sub=collections.Counter()
 for b in blocks:
  s=b
  while s:sub[s]+=1;s=(s-1)&b
 mapping=[];used=0
 def dfs(used):
  if time.monotonic()-T>108:raise TimeoutError
  t=len(mapping)
  if t==n:
   if any(mapping[i]//v!=mapping[j]//v for i in range(n) for j in range(i) if i//v==j//v):return mapping.copy()
   return
  for y in range(n):
   if used>>y&1:continue
   ok=True
   for s in range(1<<t):
    if s.bit_count()>k+e-2:continue
    sm=(1<<t)|s; im=1<<y
    for i in range(t):
     if s>>i&1:im|=1<<mapping[i]
    if sub[sm]!=sub[im]:ok=False;break
   if ok:
    mapping.append(y);r=dfs(used|1<<y);mapping.pop()
    if r:return r
 return dfs(0)
try:
 for v in range(2,6):
  for k in range(2,v+1):
   comb=list(itertools.combinations(range(v),k));count=0
   for mask in range(1,1<<len(comb)):
    bb=[comb[i] for i in range(len(comb)) if mask>>i&1];degrees=[sum(x in b for b in bb) for x in range(v)]
    if min(degrees)!=max(degrees):continue
    for e in [2,3]:
     if (e==2 and k==2) or v*e>10:continue
     total+=1;count+=1;r=check(v,k,bb,e)
     if r:print('COUNTEREXAMPLE',v,k,bb,e,r,flush=True);sys.exit()
   print(json.dumps({'v':v,'k':k,'instances_checked':count,'cumulative':total}),flush=True)
except TimeoutError: print('PARTIAL time cap',v,k,mask,e,'completed_before_current',total-1,flush=True)
