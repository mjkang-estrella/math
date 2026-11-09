# Independent exact check of the candidate counterexample to Benson-Ralli-Tetali Conjecture 4.1 (arXiv:1802.01952v2), (p,q)=(2,2).
# Graph H: Cayley graph of G=<a,c,d> <= S_5, S={a,a^-1,c,d}, a=(0 3 1 2), c=(0 3)(2 4), d=(0 2)(1 4); vertices = group elements.
# Exact lazy-1/2 Ollivier curvature per BRT Definition 2.1: mu_x = 1/2 at x, 1/(2*4) at each neighbour.
# Masses are integer multiples of 1/8 (x: 4 units, each neighbour: 1 unit), so W1 = (1/8) * min-cost assignment of 8 units to 8 units
# (integral optimal transport for integral supplies). Distances are exact BFS distances in H.
# Also checks the product H x Z (6-regular) against Z^3 using the explicit-plan lower bound and exact product distances.
import itertools,json,sys
from fractions import Fraction as F
def mul(u,v): return tuple(u[i] for i in v)
def inv(u):
    r=[0]*len(u)
    for i,x in enumerate(u): r[x]=i
    return tuple(r)
a=(3,2,0,1,4); c=(3,1,4,0,2); d=(2,4,0,3,1)
S=[a,inv(a),c,d]
e=tuple(range(5))
V=[e]; idx={e:0}; k=0
while k<len(V):
    for s in S:
        g=mul(V[k],s)
        if g not in idx: idx[g]=len(V); V.append(g)
    k+=1
n=len(V)
adj=[sorted({idx[mul(V[i],s)] for s in S}) for i in range(n)]
errs=[]
if any(len(x)!=4 or i in x for i,x in enumerate(adj)): errs.append('not simple 4-regular')
if any(i not in adj[j] for i in range(n) for j in adj[i]): errs.append('not symmetric')
def bfs(src):
    D=[-1]*n; D[src]=0; fr=[src]
    while fr:
        nf=[]
        for u in fr:
            for w in adj[u]:
                if D[w]<0: D[w]=D[u]+1; nf.append(w)
        fr=nf
    return D
dist=[bfs(i) for i in range(n)]
def kappa(x,y):
    U=[x]*4+adj[x]; W=[y]*4+adj[y]
    best=min(sum(dist[u][w] for u,w in zip(U,perm)) for perm in set(itertools.permutations(W)))
    return 1-F(best,8)
edges=sorted({(min(i,j),max(i,j)) for i in range(n) for j in adj[i]})
K={ed:kappa(*ed) for ed in edges}
def kappa_pair(x,y):
    U=[x]*4+adj[x]; W=[y]*4+adj[y]
    best=min(sum(dist[u][w] for u,w in zip(U,perm)) for perm in set(itertools.permutations(W)))
    return 1-F(best,8*dist[x][y])
allpairs=min(kappa_pair(x,y) for x in range(n) for y in range(x+1,n))
rep_extra={'min_kappa_all_pairs':str(allpairs),
 'bipartite':all((dist[0][i]+dist[0][j])%2==1 for i in range(n) for j in adj[i]),
 'triangles':sum(1 for i in range(n) for j in adj[i] for k in adj[j] if k in adj[i])//6}
if allpairs<0: errs.append('negative pair curvature')
spheres=[[sum(1 for t in dist[v] if t==r) for r in range(max(dist[v])+1)] for v in range(n)]
rep={'vertices':n,'edges':len(edges),'edge_list':edges,'min_kappa':str(min(K.values())),'kappa_values':sorted({str(v) for v in K.values()}),
     'spheres_all_vertices_identical':all(s==spheres[0] for s in spheres),'spheres':spheres[0],'Z2_spheres':[1,4,8,12]}
if min(K.values())<0: errs.append('negative curvature')
if not spheres[0][2]>8: errs.append('no excess at radius 2')
# Product H x Z: vertices (h,m); exact distance d_H + |m-m'|. Lower bound on lazy curvature via explicit plan:
# keep common mass, move (d-1)/(2d) from x to y, match A=N(x)\N[y] to B=N(y)\N[x] by a min-cost bijection; kappa >= 1-((d-1)+M)/(2d).
def nbrsP(v):
    h,m=v
    return [(w,m) for w in adj[h]]+[(h,m-1),(h,m+1)]
def dP(u,v): return dist[u[0]][v[0]]+abs(u[1]-v[1])
dd=6; worst=None
for (h0,m0) in [(0,0)]:
    x=(0,0)
    for y in nbrsP(x):
        Nx=set(nbrsP(x)); Ny=set(nbrsP(y))
        A=[u for u in Nx if u!=y and u not in Ny]; B=[u for u in Ny if u!=x and u not in Nx]
        M=min(sum(dP(u,w) for u,w in zip(A,perm)) for perm in itertools.permutations(B))
        lb=1-F((dd-1)+M,2*dd)
        worst=lb if worst is None or lb<worst else worst
# H x Z is vertex-transitive (Cayley graph of G x Z), so the edges at (0,0) cover all edge orbits.
cnt={}
for h in range(n):
    for m in range(-2,3):
        r=dist[0][h]+abs(m)
        cnt[r]=cnt.get(r,0)+1
rep['HxZ_kappa_lower_bound_min']=str(worst); rep['HxZ_spheres_r0_2']=[cnt[0],cnt[1],cnt[2]]; rep['Z3_spheres_r0_2']=[1,6,18]
if worst<0: errs.append('HxZ curvature bound negative')
if not cnt[2]>18: errs.append('HxZ no excess')
rep.update(rep_extra); rep['errors']=errs; rep['result']='PASS' if not errs else 'FAIL'
print(json.dumps(rep,sort_keys=True)); sys.exit(1 if errs else 0)
