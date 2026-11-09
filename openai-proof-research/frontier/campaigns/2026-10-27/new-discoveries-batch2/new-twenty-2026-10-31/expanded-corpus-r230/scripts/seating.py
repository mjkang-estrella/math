import math,itertools,functools,json,sys
for v in map(int,sys.argv[1:]):
 n=v//2;ds=[d for d in range(1,n+1) if math.gcd(v,d)==1];done=0;calls=0
 for L in itertools.combinations_with_replacement(ds,n):
  counts=tuple(L.count(d) for d in ds)
  @functools.lru_cache(None)
  def go(mask,cs):
   global calls
   calls+=1
   if not mask:return True
   opts=None
   for a in range(1,v):
    if not (mask>>a)&1:continue
    choices=[]
    for i,d in enumerate(ds):
     if not cs[i]:continue
     for b in ((a+d)%v,(a-d)%v):
      if (mask>>b)&1:choices.append((i,a,b))
    if opts is None or len(choices)<len(opts):opts=choices
    if not opts:return False
   for i,a,b in opts:
    cc=list(cs);cc[i]-=1
    if go(mask^(1<<a)^(1<<b),tuple(cc)):return True
   return False
  ok=go(((1<<v)-1)^1,counts)
  if not ok:print(json.dumps(dict(counterexample=L,v=v)),flush=True);sys.exit(1)
  done+=1
  if done%10000==0:print(json.dumps(dict(v=v,completed=done,calls=calls,partial=True)),flush=True)
 print(json.dumps(dict(v=v,n=n,units=ds,lists=done,calls=calls,expected=math.comb(n+len(ds)-1,len(ds)-1),all_realized=True)),flush=True)
