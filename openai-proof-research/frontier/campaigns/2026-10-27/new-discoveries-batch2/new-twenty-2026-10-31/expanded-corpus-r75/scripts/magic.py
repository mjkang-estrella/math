import json,itertools,pathlib,time
D=pathlib.Path(__file__).resolve().parents[1];out=[]
def solve(n,ks,s):
 p=n+sum(ks);edges=[(i,(i+1)%n) for i in range(n)];j=n
 for i,k in enumerate(ks):
  for _ in range(k):edges.append((i,j));j+=1
 adj=[[] for _ in range(p)]
 for a,b in edges:adj[a].append(b);adj[b].append(a)
 order=sorted(range(p),key=lambda v:-len(adj[v]));lab=[0]*p;nodes=0
 def go(d,used,sums):
  nonlocal nodes
  nodes+=1
  if d==p:return lab.copy()
  v=order[d]
  for z in range(1,p+1):
   if used>>z&1:continue
   ss=[z+lab[w] for w in adj[v] if lab[w]]
   if any(t<s or t>=s+p or sums>>t&1 for t in ss) or len(set(ss))!=len(ss):continue
   lab[v]=z
   r=go(d+1,used|1<<z,sums|sum(1<<t for t in ss))
   if r:return r
   lab[v]=0
  return None
 r=go(0,0,0);return r,nodes,edges
for n in [3,5,7]:
 for p in range(n,min(n+7,13)):
  # All weak compositions, modulo dihedral symmetry, of p-n leaves.
  def comps(total,k):
   if k==1:yield (total,);return
   for x in range(total+1):
    for r in comps(total-x,k-1):yield (x,)+r
  for ks in comps(p-n,n):
   if ks!=min(t[i:]+t[:i] for t in [ks,ks[::-1]] for i in range(n)):continue
   totalnodes=0;r=None
   for s in range(3,(n+3)//2):
    r,nodes,e=solve(n,ks,s);totalnodes+=nodes
    if r:break
   row=dict(n=n,p=p,ks=ks,nodes=totalnodes,lower_strength_witness=r,s=s if r else None)
   out.append(row);print(json.dumps(row),flush=True)
   (D/'outputs/magic-search.json').write_text(json.dumps(out,indent=2))
   if r:raise SystemExit(0)
