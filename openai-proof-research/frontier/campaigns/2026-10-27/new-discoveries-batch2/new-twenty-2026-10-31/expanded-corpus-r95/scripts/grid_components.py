import functools,json,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
flip={0:0,1:8,2:4,3:12,4:2,8:1,12:3}
def rows(v):return (1 if v&5 else 0)|(2 if v&10 else 0)
def canon(c):
 c=tuple(c);f=tuple(flip[v] for v in c);return min(c,c[::-1],f,f[::-1])
def split(c):
 out=[];part=[];last=0
 for v in c:
  r=rows(v)
  if not r or last and not last&r:
   if part:out.append(canon(part));part=[]
  if r:part.append(v)
  last=r
 if part:out.append(canon(part))
 return out
count=0
@functools.lru_cache(None)
def f(state,turn):
 global count
 count+=1
 if count>600000:raise RuntimeError('600000 state cap')
 vals=[]
 for ic,c in enumerate(state):
  for col,v in enumerate(c):
   for row,bit in [(0,1),(1,8)] if turn==0 else [(0,4),(1,2)]:
    if not v&bit:continue
    new=list(c);score=0
    for j,r in [(col,row),(col,1-row),(col-1,row),(col+1,row)]:
     if 0<=j<len(c):
      mask=5 if r==0 else 10
      if new[j]&mask:score+=1;new[j]&=~mask
    nxt=tuple(sorted(list(state[:ic])+list(state[ic+1:])+split(new)))
    vals.append((1 if turn==0 else -1)*score+f(nxt,1-turn))
 if not vals:return (-1 if turn==0 else 1)*sum(v.bit_count() for c in state for v in c)
 return max(vals) if turn==0 else min(vals)
for m in [2,3,4,5,6,8,10,12,16,32]:
 state=(canon([3 if i%2==0 else 12 for i in range(m)]),);start=count
 try:value=f(state,0);print(json.dumps({'m':m,'score':value,'complete':True,'new_states':count-start,'total_states':count}),flush=True)
 except RuntimeError as e:print(json.dumps({'m':m,'complete':False,'error':str(e),'total_states':count}),flush=True);break
