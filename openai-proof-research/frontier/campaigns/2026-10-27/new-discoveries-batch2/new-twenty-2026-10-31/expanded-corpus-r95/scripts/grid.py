import functools,json,resource,time
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
for m in [2,3,4,5,6,7,8,10,32]:
 adj=[];colors=[0,0]
 for i in range(2*m):
  row,col=divmod(i,m);colors[(row+col)%2]|=1<<i;neigh=1<<(m*(1-row)+col)
  if col:neigh|=1<<(i-1)
  if col+1<m:neigh|=1<<(i+1)
  adj.append(neigh|1<<i)
 count=0
 @functools.lru_cache(None)
 def f(mask,turn):
  global count
  count+=1
  if count>250000:raise RuntimeError('state cap 250000')
  moves=mask&colors[turn]
  if not moves:return (-1 if turn==0 else 1)*mask.bit_count()
  best=-1000 if turn==0 else 1000
  while moves:
   bit=moves&-moves;moves-=bit;i=bit.bit_length()-1;take=mask&adj[i];val=(1 if turn==0 else -1)*take.bit_count()+f(mask^take,1-turn)
   best=max(best,val) if turn==0 else min(best,val)
  return best
 try:val=f((1<<(2*m))-1,0);print(json.dumps({'m':m,'left_score':val,'states':count,'complete':True}),flush=True)
 except RuntimeError as e:print(json.dumps({'m':m,'states':count,'complete':False,'error':str(e)}),flush=True)
 f.cache_clear()
