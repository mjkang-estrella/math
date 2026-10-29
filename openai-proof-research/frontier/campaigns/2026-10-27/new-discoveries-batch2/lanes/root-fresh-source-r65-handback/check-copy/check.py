import itertools,json,time,sys
from pathlib import Path
P=Path(__file__).resolve().parent
n=int(sys.argv[1]) if len(sys.argv)>1 else 6
assert 2<=n<=6
perms=list(itertools.permutations(range(n)))
masks=[sum(1<<(n*c+x) for c,x in enumerate(p)) for p in perms]
compat=[[(j,sum(x<y for x,y in zip(p,q))) for j,q in enumerate(perms) if not masks[i]&masks[j]] for i,p in enumerate(perms)]
counts=[0]*(n*(n-1)+1);nodes=[0]*n
start=time.monotonic()
def visit(prev,used,k,s):
 nodes[k-1]+=1
 if k==n:
  counts[s]+=1;return
 for j,a in compat[prev]:
  if not used&masks[j]:visit(j,used|masks[j],k+1,s+a)
visit(0,masks[0],1,0)
assert counts==counts[::-1]
known={2:1,3:2,4:24,5:1344,6:1128960}
assert sum(counts)==known[n]
interior=counts[n+1:(n-1)**2-1]
mode=max(range(len(interior)),key=interior.__getitem__) if interior else 0
unimodal=all(interior[i]<=interior[i+1] for i in range(mode)) and all(interior[i]>=interior[i+1] for i in range(mode,len(interior)-1))
out=dict(n=n,first_row_normalized_counts=counts,total=sum(counts),nodes=nodes,interior_unimodal=unimodal,elapsed=time.monotonic()-start)
(P/f'checks-n{n}.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
