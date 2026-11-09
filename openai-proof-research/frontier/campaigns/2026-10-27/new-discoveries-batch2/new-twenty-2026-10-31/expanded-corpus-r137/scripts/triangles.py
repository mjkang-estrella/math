# 363690: search H = (t triangles) + paths, all perfect gluings of vertex-disjoint triangles,
# for a non-3-colourable G. With t <= 2 the path-linked restriction is vacuous.
import sys,itertools,json,time
def perfect_packings(verts):
    if not verts: yield []; return
    a=verts[0]; rest=verts[1:]
    for i in range(len(rest)):
        for j in range(i+1,len(rest)):
            b,c=rest[i],rest[j]
            rem=[v for k,v in enumerate(rest) if k!=i and k!=j]
            for p in perfect_packings(rem): yield [(a,b,c)]+p
def colourable(n,adj):
    order=sorted(range(n),key=lambda v:-len(adj[v])); col=[-1]*n
    # DSATUR-lite backtracking
    def bt(k):
        if k==n: return True
        # pick uncoloured vertex with most coloured-distinct neighbours
        best=None;bs=-1
        for v in range(n):
            if col[v]<0:
                s=len({col[u] for u in adj[v] if col[u]>=0})
                if s>bs: bs=s;best=v
        v=best
        used={col[u] for u in adj[v]}
        for c in range(3):
            if c not in used:
                col[v]=c
                if bt(k+1): return True
        col[v]=-1; return False
    return bt(0)
def build(tri,paths):
    edges=set(); n=0; tris=[]
    for _ in range(tri):
        a,b,c=n,n+1,n+2; edges|={(a,b),(b,c),(a,c)}; tris.append((a,b,c)); n+=3
    pathv=[]
    for L in paths:  # L = number of vertices
        vs=list(range(n,n+L)); pathv.append(vs)
        for x,y in zip(vs,vs[1:]): edges.add((x,y))
        n+=L
    return n,edges,tris,pathv
tri=int(sys.argv[1]); paths=[int(x) for x in sys.argv[2].split(',')] if sys.argv[2] else []
n,E,tris,pathv=build(tri,paths)
assert n%3==0
cnt=0;bad=[]
t=time.time()
for P in perfect_packings(list(range(n))):
    cnt+=1
    adj=[set() for _ in range(n)]
    for (x,y) in E: adj[x].add(y);adj[y].add(x)
    for (a,b,c) in P:
        for x,y in ((a,b),(b,c),(a,c)): adj[x].add(y);adj[y].add(x)
    if not colourable(n,adj):
        bad.append(P)
        if len(bad)>=3: break
print(json.dumps({'triangles':tri,'path_vertex_counts':paths,'n':n,'packings_checked':cnt,'non3col_found':len(bad),'examples':bad,'seconds':round(time.time()-t,1)}))
