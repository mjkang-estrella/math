import random,itertools,json,resource,time
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));rng=random.Random(95003)
def count(n,es,limit=2):
 m=len(es);par=list(range(m))
 def find(p,x):
  while p[x]!=x:x=p[x]
  return x
 def union(p,x,y):p[find(p,x)]=find(p,y)
 idx={tuple(sorted(e)):i for i,e in enumerate(es)}
 for a,b,c in itertools.combinations(range(n),3):
  if all(e in idx for e in [(a,b),(a,c),(b,c)]):union(par,idx[a,b],idx[a,c]);union(par,idx[a,b],idx[b,c])
 groups={}
 for i in range(m):groups.setdefault(find(par,i),[]).append(i)
 groups=sorted(groups.values(),key=lambda g:-len(g));ans=0;nodes=0
 def dfs(i,red,blue,used):
  nonlocal ans,nodes
  nodes+=1
  if nodes>30000:raise TimeoutError
  if i==len(groups):ans+=used==3;return
  for color in ([0] if i==0 else [0,1]):
   r=red[:];b=blue[:];p=r if color==0 else b
   for e in groups[i]:union(p,*es[e])
   good=True
   for j in range(i+1):
    # assigned colours tracked externally
    co=color if j==i else colors[j]
    other=b if co==0 else r
    if any(find(other,es[e][0])==find(other,es[e][1]) for e in groups[j]):good=False;break
   if good:
    colors[i]=color;dfs(i+1,r,b,used|1<<color)
   if ans>=limit:return
 colors=[0]*len(groups)
 try:dfs(0,list(range(n)),list(range(n)),0);return ans,nodes,True
 except TimeoutError:return ans,nodes,False

def zero(es,n):
 from functools import lru_cache
 @lru_cache(None)
 def f(mask,opened):
  vs=[v for v in range(n) if mask>>v&1]
  if len(vs)==2:return opened==1
  for v in vs:
   ns=[b if a==v else a for a,b in es if (a==v or b==v) and mask>>a&1 and mask>>b&1]
   if len(ns)==2:
    op=int(tuple(sorted(ns)) not in es)
    if opened+op<=1 and f(mask^(1<<v),opened+op):return True
  return False
 return f((1<<n)-1,0)
def stable(n,es):
 for mask in range(1,1<<n):
  if any(mask>>a&1 and mask>>b&1 for a,b in es):continue
  left=[v for v in range(n) if not mask>>v&1]
  if len(left)<2:continue
  seen={left[0]}
  while True:
   ns=seen|{v for u,v in es if u in seen and v in left}|{u for u,v in es if v in seen and u in left}
   if ns==seen:break
   seen=ns
  if len(seen)!=len(left):return True
 return False
for n in [6,7,8,9,10,11,12,14,16]:
 hist={};unique=[];incomplete=0;nodes=0
 for rep in range(240):
  es={(0,1),(1,2),(0,2)}
  for v in range(3,n):
   if rng.random()<.45:
    a,b=rng.sample(range(v),2);es|={tuple(sorted((a,v))),tuple(sorted((b,v)))}
   else:
    a,b=rng.choice(sorted(es));c=rng.choice([x for x in range(v) if x not in [a,b]]);es.remove((a,b));es|={(a,v),(b,v),(c,v)}
  es=sorted(es);c,nd,complete=count(n,es);nodes+=nd;hist[c]=hist.get(c,0)+1
  if not complete:incomplete+=1
  if complete and c==1:
   z=zero(es,n);st=stable(n,es) if not z else None
   unique.append({'edges':es,'one_open_zero_extension':z,'stable_cut_if_not_zero':st})
 print(json.dumps({'n':n,'sampled':240,'hist_count_capped_at_2':hist,'node_cap_incomplete':incomplete,'dfs_nodes':nodes,'unique':unique}),flush=True)
