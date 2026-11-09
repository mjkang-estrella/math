import itertools,json
for target in [[(0,1),(1,2)]]+[list(p) for p in itertools.permutations([(0,1),(1,2),(2,3)])]:
 tnv=max(max(e) for e in target)+1
 for n in range(tnv,6):
  es=list(itertools.combinations(range(n),2));maps=[]
  for p in itertools.permutations(range(n),tnv):maps.append([tuple(sorted((p[u],p[v]))) for u,v in target])
  def has(h):
   for mp in maps:
    vals=[h.get(e,-100) for e in mp]
    if min(vals)>=0 and all(x<y for x,y in zip(vals,vals[1:])):return True
   return False
  tried=0;found=None
  for k in range(0,len(es)+1):
   for seq in itertools.permutations(es,k):
    tried+=1;h={e:i+1 for i,e in enumerate(seq)}
    if has(h):continue
    if all(has(dict(h,**{} )|{e:0}) for e in es if e not in h):found=seq;break
   if found is not None:break
  print(json.dumps(dict(target=target,n=n,sat_m=k,tried_ordered_hosts=tried,witness=found)),flush=True)
