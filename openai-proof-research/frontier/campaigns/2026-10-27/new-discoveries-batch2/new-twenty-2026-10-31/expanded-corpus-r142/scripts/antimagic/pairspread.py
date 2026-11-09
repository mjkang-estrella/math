# Minimum spread of q distinct pair sums over pairings of [1,2q]. Exhaustive DFS.
import sys,json
def best(q):
  N=2*q; bestv=[10**9,None]
  used=[False]*(N+1)
  def dfs(sums,pairs):
    # pick smallest unused
    i=next((x for x in range(1,N+1) if not used[x]),None)
    if i is None:
      sp=max(sums)-min(sums)
      if sp<bestv[0]: bestv[0]=sp; bestv[1]=list(pairs)
      return
    used[i]=True
    for j in range(i+1,N+1):
      if not used[j] and (i+j) not in sums:
        s=sums|{i+j}
        if max(s)-min(s)>=bestv[0]: continue
        used[j]=True; pairs.append((i,j)); dfs(s,pairs); pairs.pop(); used[j]=False
    used[i]=False
  dfs(frozenset(),[])
  return bestv
for q in range(2,int(sys.argv[1])+1):
  b=best(q); print(json.dumps(dict(q=q,min_spread=b[0],pairs=b[1])),flush=True)
