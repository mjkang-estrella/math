import itertools,json,time,sys
# rows indexed bottom-up, both left and right endpoints weakly increasing
out=[]
for n in range(2,int(sys.argv[1])+1):
 start=time.time();tested=0;perms=0;minimum=0;hist={}
 pp=list(itertools.permutations(range(n)));subs={k:list(itertools.combinations(range(n),k)) for k in range(2,n+1)}
 for left in itertools.combinations_with_replacement(range(n),n):
  if left[0]!=0:continue
  for right in itertools.combinations_with_replacement(range(n),n):
   if right[-1]!=n-1 or any(a>b for a,b in zip(left,right)):continue
   counts=[[0,0] for k in range(n+1)];valid=0
   for p in pp:
    if any(not left[i]<=p[i]<=right[i] for i in range(n)):continue
    valid+=1
    for k,ss in subs.items():
     inc=dec=False
     for ix in ss:
      v=[p[i] for i in ix]
      if not all(left[i]<=min(v) and max(v)<=right[i] for i in ix):continue
      inc|=all(v[j]<v[j+1] for j in range(k-1));dec|=all(v[j]>v[j+1] for j in range(k-1))
     counts[k][0]+=not inc;counts[k][1]+=not dec
   if not valid:continue
   tested+=1;perms+=valid
   for k in range(2,n+1):
    a,b=counts[k];hist[str(k)]=hist.get(str(k),0)+int(a>b)
    if a<b:
     print('COUNTEREXAMPLE',n,left,right,k,a,b,flush=True);raise RuntimeError('witness')
 row=dict(n=n,shapes_with_transversals=tested,transversals_examined=perms,strict_shapes_by_k=hist,wall=time.time()-start)
 print(row,flush=True);out.append(row);json.dump(out,open('outputs/skew.json','w'),indent=2)
