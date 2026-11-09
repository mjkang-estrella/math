import itertools,sys,time,json,pathlib
p,n=map(int,sys.argv[1:]); checked=valid=0;fails=[];t=time.time()
subsets=[s for d in range(4) for s in itertools.combinations(range(n),d)]
def reps(v):
 total=0
 for k in range(1,p):
  u=[(k*a+p//2)%p-p//2 for a in v];sq=sum(a*a for a in u);sm=sum(u)
  if sq>p*p:continue
  delta=[-p if a>0 else p for a in u];qs=[p*p-2*p*abs(a) for a in u]
  for ids in subsets:
   if sm+sum(delta[i] for i in ids)==p and sq+sum(qs[i] for i in ids)==p*p:total+=1
 return total
for v in itertools.combinations_with_replacement(range(1,p),n):
 checked+=1
 if sum(v)%p or sum(a*a for a in v)%p:continue
 valid+=1;r=reps(v)
 if (n<=8 and r!=n) or (n>=2*p+1 and r==n):
  o=dict(p=p,n=n,v=v,representatives=r);fails.append(o);print('FAIL',o,flush=True)
print(json.dumps(dict(p=p,n=n,multisets=checked,isotropic=valid,failures=fails,seconds=time.time()-t)),flush=True)
