import random,functools,json,pathlib,sys
L=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(148);out=[]
def count(up,mode):
 n=len(up);full=(1<<n)-1;pair=[[0]*n for _ in range(n)]
 comp=lambda a,b: bool(up[a]>>b&1 or up[b]>>a&1 or a==b)
 for x in range(n):
  for y in range(n):
   for z in range(n):
    if mode==0:bad=up[x]>>y&1 and up[z]>>y&1 and not comp(x,z)
    else:bad=not comp(x,y) and up[x]>>z&1 and up[y]>>z&1
    if bad:pair[x][y]|=1<<z
 @functools.lru_cache(None)
 def rec(mask,forbid):
  if mask==full:return 1
  total=0
  for y in range(n):
   bit=1<<y
   if (mask|forbid)&bit:continue
   f=forbid
   for x in range(n):
    if mask>>x&1:f|=pair[x][y]
   total+=rec(mask|bit,f&~(mask|bit))
  return total
 return rec(0,0),rec.cache_info().currsize
for n,reps in [(8,500),(9,500),(10,250),(11,100),(12,50)]:
 for trial in range(reps):
  prob=rng.choice([.1,.2,.3,.5,.7]);up=[sum(1<<j for j in range(i+1,n) if rng.random()<prob) for i in range(n)]
  for i in range(n-1,-1,-1):
   for j in range(i+1,n):
    if up[i]>>j&1:up[i]|=up[j]
  a,sa=count(up,0);b,sb=count(up,1)
  out.append({'n':n,'trial':trial,'upper_sets':up,'hill':a,'valley':b,'states':[sa,sb]})
  if a>b:print('COUNTEREXAMPLE',out[-1],flush=True);break
 print(n,'completed',trial+1,'min_gap',min(x['valley']-x['hill'] for x in out if x['n']==n),flush=True)
 (L/'outputs/posets.json').write_text(json.dumps(out))
