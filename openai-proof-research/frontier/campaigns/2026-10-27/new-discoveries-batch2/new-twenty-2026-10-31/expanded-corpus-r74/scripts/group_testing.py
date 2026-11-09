import os,resource,pathlib,itertools,json,functools,math,time
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);D=pathlib.Path(__file__).resolve().parents[1];out=[]
for n in range(4,10):
 for k in range(2,n):
  for a in range(1,4):
   if k+math.log2(k)+1>math.ceil(n/a):continue
   possible=[s for s in range(1<<n) if s.bit_count()>=k];allstate=(1<<len(possible))-1;queries=[]
   for q in range(1,1<<n):queries.append(sum(1<<i for i,s in enumerate(possible) if (s&q).bit_count()*a>=q.bit_count()))
   queries=list(set(queries));zeroes=[sum(1<<i for i,s in enumerate(possible) if not s>>v&1) for v in range(n)];calls=[0]
   @functools.lru_cache(None)
   def can(state,depth):
    calls[0]+=1
    if any(state&z==0 for z in zeroes):return True
    if depth==0:return False
    splits=[]
    for q in queries:
     x=state&q;y=state^x
     if x and y:splits.append((max(x.bit_count(),y.bit_count()),x,y))
    splits.sort()
    for _,x,y in splits:
     if can(x,depth-1) and can(y,depth-1):return True
    return False
   lower=math.ceil(math.log2(n-k+1));upper=math.ceil(n/a)-k+math.ceil(math.log2(a));opt=None
   for depth in range(lower,upper+1):
    if can(allstate,depth):opt=depth;break
   row={'id':381127,'n':n,'k':k,'alpha':f'1/{a}','objects':len(possible),'queries':len(queries),'depth_states':calls[0],'optimum':opt,'Theorem6_bound':upper,'limitation':'Compares the stated worst-case bound, not a full reconstruction of every algorithm branch'};out.append(row);print(json.dumps(row),flush=True);(D/'outputs/group-testing.json').write_text(json.dumps(out,indent=2))
