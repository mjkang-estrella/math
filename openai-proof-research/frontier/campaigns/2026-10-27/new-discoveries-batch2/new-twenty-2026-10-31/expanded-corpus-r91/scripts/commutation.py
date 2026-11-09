import sys,pathlib,json,collections,time
D=pathlib.Path(__file__).resolve().parents[1]; n=int(sys.argv[1]); counts=collections.Counter();words={};nodes=0;t=time.monotonic()
def dfs(p,last,w):
 global nodes
 nodes+=1;counts[p]+=1
 if counts[p]==3:words[p]=list(w)
 for j in ([last-1,last+1] if last is not None else range(n-1)):
  if 0<=j<n-1 and p[j]<p[j+1]:
   a=list(p);a[j],a[j+1]=a[j+1],a[j];dfs(tuple(a),j,w+(j+1,))
dfs(tuple(range(1,n+1)),None,())
hist=collections.Counter(counts.values());hist[0]=mathfactor=__import__('math').factorial(n)-len(counts)
r=dict(n_letters=n,nodes=nodes,permutations_reached=len(counts),histogram=dict(sorted(hist.items())),three_examples=[p for p in counts if counts[p]==3],seconds=time.monotonic()-t)
print(json.dumps(r),flush=True);(D/f'outputs/commutation-{n}.json').write_text(json.dumps(r,indent=2)+'\n')
