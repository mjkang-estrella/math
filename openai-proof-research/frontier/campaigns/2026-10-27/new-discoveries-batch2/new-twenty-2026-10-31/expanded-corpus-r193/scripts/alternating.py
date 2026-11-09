import pathlib,itertools,json
D=pathlib.Path(__file__).resolve().parents[1]
def pat(v):return tuple(sum(z<x for z in v)+1 for x in v)
out=[]
for n in range(2,9):
 A=[p for p in itertools.permutations(range(1,n+1)) if all((p[i]<p[i+1])==(i%2==0) for i in range(n-1))]
 for k in range(2,min(n,4)+1):
  qs=list(itertools.permutations(range(1,k+1)));cnt=dict.fromkeys(qs,0)
  for p in A:
   seen={pat(tuple(p[i] for i in ix)) for ix in itertools.combinations(range(n),k)}
   for q in qs:cnt[q]+=q not in seen
  dec=tuple(range(k,0,-1));viol=[{'q':q,'avoid':v} for q,v in cnt.items() if v<cnt[dec]]
  out.append({'n':n,'k':k,'total_alternating':len(A),'decreasing_avoid':cnt[dec],'inequality_violations':viol})
(D/'outputs/alternating.json').write_text(json.dumps(out,indent=2));print(out[:4])
