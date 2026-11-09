import itertools,collections,json,sys,time
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def run(n):
 pairs=list(itertools.combinations(range(n),2));perms=list(itertools.permutations(range(n)));seen={};count=0
 for mask in range(1<<len(pairs)):
  a=[0]*n
  for k,(u,v) in enumerate(pairs):
   if mask>>k&1:a[u]|=1<<v
  if any(a[v]&~a[u] for u in range(n) for v in range(n) if a[u]>>v&1):continue
  sig=[0]*(1<<max(0,n-1))
  for p in perms:
   desc=sum(1<<i for i in range(n-1) if a[p[i]]>>p[i+1]&1);sig[desc]+=1
  score=sum(x==0 for x in a)+sum(not any(row>>v&1 for row in a) for v in range(n));key=tuple(sig)
  if key in seen and seen[key][0]!=score:
   print(json.dumps(dict(counterexample=True,n=n,earlier_posets_checked=count,masks=[seen[key][1],mask],sums=[seen[key][0],score],signature=sig)),flush=True);return
  seen[key]=(score,mask);count+=1
 print(json.dumps(dict(n=n,naturally_labelled_posets=count,distinct_functions=len(seen),counterexample=False)),flush=True)
if __name__=='__main__':
 for n in range(1,int(sys.argv[1])+1):run(n)
