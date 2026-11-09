# Independent bounded local search. A failure to find is NOT UNSAT evidence.
import random,time,itertools,json,pathlib,math
L=pathlib.Path(__file__).resolve().parents[1]
rng=random.Random(369421)
results=[]
for m,n in [(4,4),(3,6)]:
 N=m*n; E=set()
 for r,c in itertools.product(range(m),range(n)):
  for s,d in [((r+1)%m,c),(r,(c+1)%n)]: E.add(tuple(sorted((r*n+c,s*n+d))))
 pairs=list(itertools.combinations(range(N),2))
 def bad(w,a,b):
  z=[x for x in w if x==a or x==b]
  return all(z[i]!=z[i+1] for i in range(5)) != ((a,b) in E)
 start=time.monotonic(); best=10000; trials=0; bestword=None
 while time.monotonic()-start<8:
  w=list(range(N))*3; rng.shuffle(w)
  score=sum(bad(w,a,b) for a,b in pairs)
  for step in range(300):
   i,j=rng.sample(range(3*N),2); x,y=w[i],w[j]
   if x==y: continue
   affected=[p for p in pairs if x in p or y in p]
   old=sum(bad(w,*p) for p in affected)
   w[i],w[j]=w[j],w[i]
   new=sum(bad(w,*p) for p in affected)
   delta=new-old
   if delta<=0 or rng.random()<math.exp(-delta/max(.1,1-step/300)):
    score+=delta
   else: w[i],w[j]=w[j],w[i]
   trials+=1
   if score<best: best=score; bestword=w[:]
   if score==0: break
  if best==0: break
 if best==0:
  assert sum(bad(bestword,*p) for p in pairs)==0
 results.append(dict(m=m,n=n,seconds=time.monotonic()-start,trials=trials,best_mismatched_pairs=best,certificate=bestword if best==0 else None,status='SAT independently checked' if best==0 else 'INCONCLUSIVE bounded heuristic'))
print(json.dumps(results,indent=2))
