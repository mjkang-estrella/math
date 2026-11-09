import itertools,json,pathlib,numpy as np,scipy.sparse as sp
from scipy.sparse.csgraph import maximum_bipartite_matching
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for t in range(2,5):
 m=2*t+1;sets=[tuple(i for i in range(m) if mask>>i&1) for mask in range(1,1<<m) if all(not(mask>>i&1 and mask>>((i+1)%m)&1) for i in range(m))];tests=0
 for A in sets:
  for B in sets:
   V=[(i,j) for i in range(m) for j in range(m) if i not in A and j not in B];idx={v:i for i,v in enumerate(V)};adj=[[] for v in V]
   for q,(i,j) in enumerate(V):
    for v in [((i+1)%m,j),((i-1)%m,j),(i,(j+1)%m),(i,(j-1)%m)]:
     if v in idx:adj[q].append(idx[v])
   color={}
   for q in range(len(V)):
    if q in color:continue
    color[q]=0;Q=[q]
    for z in Q:
     for y in adj[z]:
      if y in color:assert color[y]!=color[z]
      else:color[y]=1-color[z];Q.append(y)
   L=[q for q in color if color[q]==0];R=[q for q in color if color[q]==1];ri={q:i for i,q in enumerate(R)};rr=[];cc=[]
   for i,q in enumerate(L):
    for v in adj[q]:rr.append(i);cc.append(ri[v])
   X=sp.csr_matrix((np.ones(len(rr)),(rr,cc)),shape=(len(L),len(R)));match=maximum_bipartite_matching(X,perm_type='column');alpha=len(V)-sum(match>=0)
   def odds(S):
    a=sorted(S);return sum(((a[(i+1)%len(a)]-a[i]-1)%m)%2 for i in range(len(a)))
   exact=((m-len(A))*(m-len(B))+odds(A)*odds(B))//2
   assert alpha==exact
   tests+=1
 out.append({'t':t,'independent_nonempty_cycle_sets':len(sets),'pairs':tests,'matching_equals_rectangle_formula':True})
 print(out[-1],flush=True)
(D/'outputs/wheel-matching.json').write_text(json.dumps(out,indent=2)+'\n')
