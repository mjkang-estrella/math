import pathlib,json,itertools,functools,time,math
D=pathlib.Path(__file__).resolve().parents[1];out=[];t=time.monotonic()
for n,cap in [(3,20),(4,12)]:
 N=1<<(n-1);adj=[[v^(1<<k) for k in range(n-1)] for v in range(N)];L=math.lcm(*range(1,n+1));weights=[L//(v.bit_count()+1) for v in range(N)];bound=sum(weights);tested=0;bad=0
 @functools.lru_cache(None)
 def solvable(p):
  if p[0]>=2:return True
  for u in range(N):
   if p[u]<2:continue
   for v in adj[u]:
    q=list(p);q[u]-=2;q[v]+=1
    if solvable(tuple(q)):return True
  return False
 def configs(total,dim,prefix=()):
  if dim==1:yield prefix+(total,);return
  for x in range(total+1):yield from configs(total-x,dim-1,prefix+(x,))
 rows=[]
 for total in range(cap+1):
  cnt=0
  for p in configs(total,N):
   cnt+=1;tested+=1
   if sum(a*b for a,b in zip(p,weights))>bound and not solvable(p):
    print('FAIL',n,p,flush=True);bad+=1
   if time.monotonic()-t>100:
    out.append({'n':n,'complete_through_total':total-1,'partial_total':total,'partial_count':cnt,'tested':tested,'counterexamples':bad});(D/'outputs/pebbling.json').write_text(json.dumps(out,indent=2));raise SystemExit
  rows.append({'total':total,'configurations':cnt})
 out.append({'n':n,'complete_through_total':cap,'tested':tested,'counterexamples':bad,'rows':rows});print(out[-1],flush=True)
(D/'outputs/pebbling.json').write_text(json.dumps(out,indent=2))
