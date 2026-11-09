import itertools,json,math,time

def areas(n):
 def rec(a):
  if len(a)==n:yield tuple(a);return
  for x in range(a[-1] if a else 0,len(a)+1):yield from rec(a+[x])
 yield from rec([])
def row(U,k,l):
 n=len(U)
 def arrow(a,b):return a>=b or a>=U[b]
 def esch(w):return all(arrow(w[i],w[(i+1)%len(w)]) for i in range(len(w)))
 perms=list(itertools.permutations(range(n)));big=sum(esch(w) for w in perms);counts={};pairs=0;undefined=0
 sortperms=list(itertools.permutations(range(4)))
 for w in perms:
  u,v=w[:k],w[k:]
  if not esch(u) or not esch(v):continue
  pairs+=1
  ins=next((i for i in range(math.lcm(k,l)) if arrow(u[i%k],v[(i+1)%l]) and arrow(v[i%l],u[(i+1)%k])),None)
  if ins is None:core=(0,-2,-2,-1)
  else:
   spl=next((i for i in range(k) if arrow(u[(i+l)%k],u[(i+1)%k]) and arrow(u[i],u[(i+l+1)%k])),None)
   if spl is None:undefined+=1;continue
   core=(0,-2,-2,2*ins+3) if spl==0 else (0,2*spl,2*(spl+l),2*ins+1)
  mask=sum(1<<j for j,sp in enumerate(sortperms) if all(core[a]>=core[b] for a,b in zip(sp,sp[1:])))
  counts[mask]=counts.get(mask,0)+1
 return {'area':U,'target':pairs-big,'classes':counts,'undefined':undefined}
def feasibility(rows):
 variables=sorted({j for r in rows for m in r['classes'] for j in range(24) if m>>j&1})
 def dfs(j,yes,no):
  for r in rows:
   lo=sum(c for m,c in r['classes'].items() if m&yes);hi=sum(c for m,c in r['classes'].items() if m&~no)
   if not lo<=r['target']<=hi:return None
  if j==len(variables):return yes
  bit=1<<variables[j];x=dfs(j+1,yes,no|bit)
  return x if x is not None else dfs(j+1,yes|bit,no)
 return dfs(0,0,0)
for k,l in [(3,2),(4,2),(4,3),(5,2)]:
 start=time.monotonic();rr=[row(U,k,l) for U in areas(k+l)];T=feasibility(rr)
 print(json.dumps({'partition':[k,l],'UIOs':len(rr),'undefined_cores':sum(r['undefined'] for r in rr),'sorting_subset_found':T,'rows':rr,'seconds':time.monotonic()-start}),flush=True)
