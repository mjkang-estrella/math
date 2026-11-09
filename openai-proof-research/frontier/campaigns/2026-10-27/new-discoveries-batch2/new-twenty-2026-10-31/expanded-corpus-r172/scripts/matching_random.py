import pathlib,itertools,random,math,json,time
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(172);start=time.monotonic();records=[];viol=[]
for n in [13,14,18]:
 k=3;s=2;r=1
 masks=[sum(1<<v for v in t) for t in itertools.combinations(range(n),k)];ix={v:i for i,v in enumerate(masks)};cache={};N=len(masks)
 def forbidden(union):
  if union not in cache:
   vs=[i for i in range(n) if not union>>i&1];b=0
   for t in itertools.combinations(vs,k):b|=1<<ix[sum(1<<v for v in t)]
   cache[union]=b
  return cache[union]
 U=math.comb(n-1,2);L=U-math.comb(n-3,2);base=[U]*2+[L]*(n-2);maxsize=0;count=0;best={p:0 for p in [1,2,3,8]};maxhinge=0
 for trial in range(600):
  weights=[rng.random()**(1+trial%5) for _ in range(n)]
  order=sorted(range(N),key=lambda i:sum(weights[v] for v in range(n) if masks[i]>>v&1)+(rng.random()*(trial%4)))
  fam=[];bad=0
  for i in order:
   if bad>>i&1:continue
   e=masks[i]
   for f in fam:
    if not e&f:bad|=forbidden(e|f)
   fam.append(e)
  deg=[sum(e>>v&1 for e in fam) for v in range(n)];count+=1;maxsize=max(maxsize,len(fam))
  for p in best:
   val=sum(d**p for d in deg);best[p]=max(best[p],val)
   if val>sum(d**p for d in base):viol.append({'n':n,'p':p,'family':fam,'degrees':deg})
  hinge=sum(max(0,d-L) for d in deg);maxhinge=max(maxhinge,hinge)
  if hinge>2*(U-L):viol.append({'n':n,'positive_part_only':deg})
  if time.monotonic()-start>100:break
 records.append({'n':n,'k':k,'matching_bound':s,'trials':count,'max_size':maxsize,'best_exact_degree_power':best,'star_bound':{p:sum(d**p for d in base) for p in best},'max_hinge':maxhinge,'hinge_bound':2*(U-L),'union_cache_size':len(cache)})
 if time.monotonic()-start>100:break
result={'method':'greedy maximal families excluding any third edge disjoint from an existing disjoint pair; random weighted vertex orders; seed172','records':records,'violations':viol,'seconds':time.monotonic()-start,'limitation':'Randomized family coverage only; exact degree calculations; not a proof or exhaustive search.'}
(D/'outputs/matching-random.json').write_text(json.dumps(result,indent=2));print(result)
