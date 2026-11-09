# Controls for hypergroup_search.py: source Example 2.14(1) (prisms P_n, n != 4, produce hypergroups though not
# distance regular) and Example 2.13 (binary tree, Z^2 do not); here: finite graphs where commutativity/associativity fail.
import sys
exec(open(sys.path[0]+'/hypergroup_search.py').read().split('t=time.time(); tot=0')[0])
def constants(n,adj,v0):
    D=dist_all(n,adj); I=sorted(set(D[v0]))
    cnt=lambda i,v: sum(1 for w in range(n) if D[v][w]==i)
    p={}
    for i in I:
        Si=[v for v in range(n) if D[v0][v]==i]
        for j in I:
            for k in I:
                tot=0
                for v in Si:
                    c=cnt(j,v)
                    if c==0: return None
                    tot+=F(sum(1 for w in range(n) if D[v][w]==j and D[v0][w]==k),c)
                p[(i,j,k)]=tot/len(Si)
    comm=all(p[(i,j,k)]==p[(j,i,k)] for i in I for j in I for k in I)
    assoc=all(sum(p[(h,i,l)]*p[(l,j,k)] for l in I)==sum(p[(i,j,l)]*p[(h,l,k)] for l in I) for h in I for i in I for j in I for k in I)
    return comm,assoc
def prism(m):
    adj=[[] for _ in range(2*m)]
    def E(a,b): adj[a].append(b); adj[b].append(a)
    for i in range(m): E(i,(i+1)%m); E(m+i,m+(i+1)%m); E(i,m+i)
    return 2*m,adj
for m in (3,5,6,7):
    n,adj=prism(m); print('prism',m,'(comm,assoc) at v0=0:',constants(n,adj,0),'S1S2:',check(n,adj,0,dist_all(n,adj)) is not None)
# path P4 from an end, and a 'paw' graph: expected failures somewhere
for name,n,E in [('path4',4,[(0,1),(1,2),(2,3)]),('paw',4,[(0,1),(1,2),(2,0),(2,3)]),('K1,3 leaf',4,[(1,0),(1,2),(1,3)])]:
    adj=[[] for _ in range(n)]
    for a,b in E: adj[a].append(b); adj[b].append(a)
    for v0 in range(n): print(name,'v0',v0,constants(n,adj,v0))
