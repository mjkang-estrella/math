import itertools as it,json,time,sys
from pathlib import Path
L=Path(__file__).resolve().parent
def std(t):
 s=sorted(t); d={x:i for i,x in enumerate(s)};return tuple(d[x] for x in t)
def run(k):
 start=time.monotonic(); ps=list(it.permutations(range(k)));idx={p:i for i,p in enumerate(ps)};rev=[idx[p[::-1]] for p in ps];cmb=list(it.combinations(range(2*k),k));families={}
 for p in ps:
  for i in range(k+1):
   for j in range(k+1):
    for sign in [1,-1]:
     outside=[x if x<j else x+k for x in p];block=list(range(j,j+k))[::sign];t=outside[:i]+block+outside[i:]; mask=0
     for c in cmb:mask|=1<<idx[std(tuple(t[a] for a in c))]
     families.setdefault(mask,dict(p=p,i=i,j=j,sign=sign,t=t))
 separators=[[] for _ in ps]
 for mask in families:
  for a in range(len(ps)):
   if (mask>>a)&1 and not ((mask>>rev[a])&1):separators[a].append(mask)
 failures=[];trials=0
 for mask,seed in families.items():
  sym=mask
  for a in range(len(ps)):
   if (mask>>a)&1:sym|=1<<rev[a]
  for a in range(len(ps)):
   if (mask>>a)&1 and (mask>>rev[a])&1:
    trials+=1
    if not any(s&~sym==0 for s in separators[a]):
     failures.append(dict(pattern=ps[a],seed=seed,allowed=[ps[b] for b in range(len(ps)) if (sym>>b)&1],mask=mask,sym=sym))
 return dict(k=k,families=len(families),trials=trials,failures=failures,seconds=time.monotonic()-start)
ks=[int(x) for x in sys.argv[1:]] or [3,4,5]
out=[run(k) for k in ks]
(L/('diagnostics-'+ '-'.join(map(str,ks))+'.json')).write_text(json.dumps(out,indent=2)+'\n')
print([(r['k'],r['families'],r['trials'],len(r['failures']),r['seconds']) for r in out])
