import sys, itertools
exec(open(sys.path[0]+'/hypergroup_search.py').read().split('t=time.time(); tot=0')[0])
A=[[1,2,3],[0,4,5],[0,6,7],[0,8,9],[1,6,10],[1,8,11],[2,4,11],[2,9,10],[3,5,10],[3,7,11],[4,7,8],[5,6,9]]
n=len(A); D=dist_all(n,A)
print('S1S2 at each vertex:',[check(n,A,v,D) is not None for v in range(n)])
print('distance profiles:',sorted(set(tuple(sorted(D[v])) for v in range(n))))
# triangles / girth
tri=sum(1 for a in range(n) for b in A[a] for c in A[b] if c in A[a])//6
print('triangles',tri,'diameter',max(max(r) for r in D))
# automorphism orbit of vertex 0 via simple backtracking
def autos_orbit():
    orb=set()
    for t in range(n):
        m={0:t}; 
        def rec(m):
            if len(m)==n: return True
            v=next(v for v in range(n) if v not in m and any(w in m for w in A[v]))
            for c in range(n):
                if c in m.values(): continue
                if all((m[w] in A[c])==(w in A[v]) for w in m) and D[0][v]==D[t][c]:
                    m[v]=c
                    if rec(m): return True
                    del m[v]
            return False
        if rec(m): orb.add(t)
    return orb
print('orbit of 0 under Aut:',sorted(autos_orbit()))
