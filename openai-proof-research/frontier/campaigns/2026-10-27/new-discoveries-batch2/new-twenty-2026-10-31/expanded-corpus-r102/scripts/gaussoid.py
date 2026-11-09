import itertools,random,json,time
random.seed(102)
for n,samples in [(5,100),(6,30)]:
 start=time.monotonic();cis=[(i,j,K) for i in range(n) for j in range(i+1,n) for K in range(1<<n) if not K&(1<<i|1<<j)];idx={c:k for k,c in enumerate(cis)}
 def bit(i,j,K):return 1<<idx[min(i,j),max(i,j),K]
 horns=[];splits=[]
 for i,j,k in itertools.permutations(range(n),3):
  for L in range(1<<n):
   if L&(1<<i|1<<j|1<<k):continue
   a,b,c,d=bit(i,j,L),bit(i,k,L),bit(i,j,L|1<<k),bit(i,k,L|1<<j)
   horns.extend([(a|d,b|c),(c|d,a|b),(a|b,c|d)])
   splits.append((a|c,bit(i,k,L)|bit(j,k,L)))
 horns=list(set(horns));splits=list(set(splits))
 def force(mask,budget):
  budget[0]+=1
  if budget[0]>2000:raise RuntimeError('branch cap')
  while True:
   old=mask
   for pre,post in horns:
    if mask&pre==pre:mask|=post
   if old==mask:break
  for pre,post in splits:
   if mask&pre==pre and not mask&post:
    x=post&-post;return force(mask|x,budget)&force(mask|(post^x),budget)
  return mask
 def glob(edges):
  par=[set() for _ in range(n)]
  for a,b in edges:par[b].add(a)
  result=0
  for z,(a,b,K) in enumerate(cis):
   anc={a,b}|{i for i in range(n) if K>>i&1};old=set()
   while old!=anc:
    old=anc.copy()
    for v in list(anc):anc|=par[v]
   adj={v:set() for v in anc}
   for v in anc:
    for p in par[v]:adj[v].add(p);adj[p].add(v)
    for x,y in itertools.combinations(par[v],2):adj[x].add(y);adj[y].add(x)
   seen={a};todo=[a]
   while todo:
    v=todo.pop()
    for w in adj[v]-seen:
     if not K>>w&1:seen.add(w);todo.append(w)
   if b not in seen:result|=1<<z
  return result
 count=0;checked=0;fails=[];caps=0
 for it in range(samples):
  edges=[(a,b) for a in range(n) for b in range(a+1,n) if random.random()<.28];g=glob(edges)
  paths={}
  for s in range(n):
   paths[s,s]=[()]
   for t in range(s+1,n):paths[s,t]=[path+((a,t),) for a,b in edges if b==t for path in paths.get((s,a),[])]
  for a,b in itertools.combinations(range(n),2):
   treks=[x+y for s in range(min(a,b)+1) for x in paths.get((s,a),[]) for y in paths.get((s,b),[])]
   if len(treks)!=1:continue
   affected=set(treks[0]);semantic=(1<<len(cis))-1
   for e in affected:semantic&=glob([x for x in edges if x!=e])
   try:formal=force(g|bit(a,b,0),[0])
   except RuntimeError:caps+=1;continue
   count+=1;checked+=semantic.bit_count()
   if semantic&~formal:fails.append({'edges':edges,'extra':(a,b,0),'missing':[cis[z] for z in range(len(cis)) if semantic&~formal>>z&1]})
 print(json.dumps({'n':n,'dag_samples':samples,'unique_trek_marginal_extras':count,'semantic_CI_conclusions_tested':checked,'branch_caps':caps,'failures':fails,'seconds':time.monotonic()-start}),flush=True)
