import itertools,functools,json,pathlib,sys,time,random
D=pathlib.Path(__file__).resolve().parents[1];mode=sys.argv[1]
if mode=='groups':
 out=[]
 for mods in [(2,3,3),(4,3,3)]:
  G=list(itertools.product(*[range(m) for m in mods]));R=[x for x in G if any(x) and any(2*a%m for a,m in zip(x,mods))];N=len(R);zero=(0,)*len(mods);idx={x:i for i,x in enumerate(R)}
  def plus(a,b):return tuple((x+y)%m for x,y,m in zip(a,b,mods))
  # Large group: only 2/3-part partitions, small group: every partition.
  sizes=range(2,N+1) if N<20 else [2,3]
  subs={k:[] for k in sizes}
  if N<20:
   sums=[zero]*(1<<N)
   for mask in range(1,1<<N):
    bit=mask&-mask;sums[mask]=plus(sums[mask^bit],R[bit.bit_length()-1])
    if sums[mask]==zero and mask.bit_count()>=2:subs[mask.bit_count()].append(mask)
  else:
   for k in sizes:
    for c in itertools.combinations(range(N),k):
     s=zero
     for i in c:s=plus(s,R[i])
     if s==zero:subs[k].append(sum(1<<i for i in c))
  @functools.lru_cache(None)
  def solve(mask,parts):
   if not parts:return not mask
   k=parts[0]
   if len(parts)==1:return mask in sets[k]
   for s in subs[k]:
    if s&mask==s and solve(mask^s,parts[1:]):return True
   return False
  sets={k:set(v) for k,v in subs.items()}
  def parts(n,lo=2):
   if n==0:yield ();return
   for k in sizes:
    if lo<=k<=n:
     for t in parts(n-k,k):yield (k,)+t
  results=[]
  for p in parts(N):
   ok=solve((1<<N)-1,tuple(sorted(p,reverse=True)));results.append({'parts':p,'exists':ok});print(mods,p,ok,flush=True)
  out.append({'moduli':mods,'R_size':N,'coverage':'all integer partitions' if N<20 else 'only parts 2 and 3','results':results});(D/'outputs/groups.json').write_text(json.dumps(out,indent=2)+'\n')
if mode=='rainbow':
 out=[]
 def trees(n):
  for root in range(n):
   vs=[i for i in range(n) if i!=root]
   for ps in itertools.product(range(n),repeat=n-1):
    par=dict(zip(vs,ps));ok=True
    for v in vs:
     seen=set();w=v
     while w!=root:
      if w in seen:ok=False;break
      seen.add(w);w=par[w]
     if not ok:break
    if ok:yield tuple((par[v],v) for v in vs)
 def exists(ts,n):
  for arcs in itertools.product(*ts):
   if len(set(v for u,v in arcs))!=n-1:continue
   root=next(iter(set(range(n))-set(v for u,v in arcs)));seen={root}
   for _ in range(n):seen|={v for u,v in arcs if u in seen}
   if len(seen)==n:return True
  return False
 for n in [2,3,4,5]:
  ts=list(trees(n));count=0;bad=None;rng=random.Random(176)
  seq=itertools.combinations_with_replacement(range(len(ts)),n-1) if n<5 else (tuple(rng.randrange(len(ts)) for _ in range(n-1)) for z in range(20000))
  for c in seq:
   count+=1
   if not exists([ts[i] for i in c],n):bad=c;break
  out.append({'n':n,'arborescences':len(ts),'families':count,'scope':'exhaustive colour-multisets' if n<5 else '20000 seeded random families','failure':bad});print(out[-1],flush=True);(D/'outputs/rainbow.json').write_text(json.dumps(out,indent=2)+'\n')
if mode=='words':
 s='010'
 for _ in range(31):s=''.join('010' if s[i]=='0' else '101' for i in range(0,len(s)-1,2))
 out=[]
 for k in range(1,17):
  last={};gap={}
  for i in range(len(s)-k+1):
   w=s[i:i+k]
   if w in last:gap[w]=max(gap.get(w,0),i-last[w])
   last[w]=i
  out.append({'length':k,'distinct':len(last),'largest_observed_gap':max(gap.values()),'singletons':sum(w not in gap for w in last)})
 (D/'outputs/words.json').write_text(json.dumps({'prefix_length':len(s),'results':out,'limitation':'finite prefix cannot settle uniform recurrence'},indent=2)+'\n');print(len(s),out,flush=True)
if mode=='overpart':
 N=2000;a=[0]*(N+1);a[0]=1
 for k in range(1,N+1):
  if k%4==0 or k%9==0:continue
  b=a[:]
  for n in range(k,N+1):b[n]=a[n]+a[n-k]+b[n-k]
  a=b
 fails=[(n,a[n],a[n]%6) for n in range(4,N+1,4) if a[n]%6]
 (D/'outputs/overpart.json').write_text(json.dumps({'N':N,'failures':fails[:20],'checked':N//4,'first_values':[a[n] for n in range(4,65,4)]},indent=2)+'\n');print(fails[:5],flush=True)
