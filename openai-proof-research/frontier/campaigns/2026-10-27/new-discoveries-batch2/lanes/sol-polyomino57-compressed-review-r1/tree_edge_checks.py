"""Exhaustive tiny models of the potential lemma, independent of certificate data."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import resource,signal
resource.setrlimit(resource.RLIMIT_AS,(536870912,)*2);resource.setrlimit(resource.RLIMIT_CPU,(160,165));signal.alarm(175)
import itertools,json,pathlib,time
start=time.monotonic();systems=treesets=root_empty=overlap=0
# All unlabeled tree shapes on four vertices: path and claw.
for edges in [[(0,1),(1,2),(2,3)],[(0,1),(0,2),(0,3)]]:
 adj=[{b for a,b in edges if a==v}|{a for a,b in edges if b==v} for v in range(4)]
 connected=[]
 for t in range(1,16):
  vertices={v for v in range(4) if t>>v&1};seen={min(vertices)}
  while True:
   more=seen|{w for v in seen for w in adj[v] if w in vertices}
   if seen==more:break
   seen=more
  if seen==vertices:connected.append((t,vertices,len(vertices)))
 for groups in itertools.product(range(1,16),repeat=3):
  systems+=1
  if any(groups[i]&groups[j] for i in range(3) for j in range(i)):overlap+=1
  D={}
  for m in range(1,8):
   for v in range(4):
    D[m,v]=min(size for t,vs,size in connected if v in vs and all(t&groups[g] for g in range(3) if m>>g&1))
  # Compute exact potentials by enumerating small connected vertex sets only.
  for m in range(1,8):
   for v in range(4):
    if all(groups[g]>>v&1 for g in range(3) if m>>g&1):assert D[m,v]==1
   for v,w in edges:assert abs(D[m,v]-D[m,w])<=1
  for a in range(1,8):
   for b in range(1,8):
    if not a&b:
     for v in range(4):assert D[a|b,v]<=D[a,v]+D[b,v]-1
  for t,vs,size in connected:
   if not all(t&g for g in groups):continue
   # Pick witnesses once, even when a vertex is in multiple groups.
   assigned={v:sum(1<<i for i,g in enumerate(groups) if min(w for w in vs if g>>w&1)==v) for v in vs}
   for root in vs:
    if not assigned[root]:root_empty+=1
    def visit(v,parent):
     mask=assigned[v];cost=1 if mask else 0
     if mask:assert D[mask,v]<=1
     for w in sorted(adj[v]&vs):
      if w==parent:continue
      child,bound=visit(w,v)
      if not child:continue
      assert D[child,v]<=D[child,w]+1<=bound+1
      if mask:
       assert not mask&child
       assert D[mask|child,v]<=D[mask,v]+D[child,v]-1
       cost+=bound
      else:cost=bound+1
      mask|=child
      assert D[mask,v]<=cost
     return mask,cost
    mask,cost=visit(root,-1)
    assert mask==7 and D[7,root]<=cost<=size
    treesets+=1
# Integer normalization translations with arbitrary negative extrema.
translations=0
for minu in range(-20,21):
 for minv in range(-20,21):
  e=(minv-minu)%2;du=-minu;dv=e-minv
  assert (du+dv)%2==0 and (du-dv)%2==0
  dx=(du+dv)//2;dy=(du-dv)//2
  assert dx+dy==du and dx-dy==dv
  translations+=1
out={'status':'PASS','systems':systems,'overlapping_group_systems':overlap,'rooted_hitting_trees_checked':treesets,'empty_root_assignment_cases':root_empty,'integer_translation_pairs':translations,'seconds':time.monotonic()-start,'scope':'All 3 labeled nonempty group memberships on each of the two 4-vertex tree shapes; all connected hitting subtrees and roots; smallest-vertex witness assignments. Finite diagnostic of ordinary induction, not a generic proof.'}
(pathlib.Path(__file__).parent/'tree-edge-evidence.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
