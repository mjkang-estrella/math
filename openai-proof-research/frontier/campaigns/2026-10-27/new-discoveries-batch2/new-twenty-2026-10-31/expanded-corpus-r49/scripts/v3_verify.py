# Independent brute-force verifier (point-based triangle definition of arXiv:2208.06912 Def. in Sec. 4).
import itertools, json, sys
def verify(lines):
    lines=[frozenset(l) for l in lines]; pts=sorted(set().union(*lines)); n=len(lines)
    inc={p:[i for i,l in enumerate(lines) if p in l] for p in pts}
    sym = len(pts)==n and all(len(l)==3 for l in lines) and all(len(inc[p])==3 for p in pts)
    linear = all(len(a&b)<=1 for a,b in itertools.combinations(lines,2))
    def line_through(a,b):
        L=[i for i,l in enumerate(lines) if a in l and b in l]; return L[0] if L else None
    tris=[]
    for a,b,c in itertools.combinations(pts,3):
        l1,l2,l3=line_through(a,b),line_through(b,c),line_through(a,c)
        if None not in (l1,l2,l3) and c not in lines[l1] and a not in lines[l2] and b not in lines[l3]:
            tris.append((a,b,c,l1,l2,l3))
    # maximum set of pairwise intersecting lines, brute force over all subsets
    omega=max(len(S) for k in range(n+1) for S in itertools.combinations(range(n),k)
              if all(lines[i]&lines[j] for i,j in itertools.combinations(S,2))) if n<=16 else None
    best=None
    for col in range(1<<n):
        m=sum(1 for t in tris if ((col>>t[3])&1)==((col>>t[4])&1)==((col>>t[5])&1))
        if best is None or m<best: best=m
    return {'points':len(pts),'lines':n,'symmetric_v3':sym,'linear':linear,'triangles':len(tris),'max_intersecting':omega,'min_mono_triangles':best}
if __name__=='__main__':
    cands={'candidate_A':[[0,2,3],[2,4,5],[3,5,8],[2,7,8],[1,3,6],[0,6,8],[0,1,4],[4,6,7],[1,5,7]],
           'pappus':[[1,2,3],[4,5,6],[7,8,9],[1,5,9],[1,6,8],[2,4,9],[2,6,7],[3,4,8],[3,5,7]],
           'fano':[[1,2,3],[1,4,5],[1,6,7],[2,4,6],[2,5,7],[3,4,7],[3,5,6]],
           'source_ex1':[[1,2,3],[3,4,5],[1,5,6],[3,6,7],[2,5,7],[1,8,9],[6,9,10],[2,11,13],[7,12,13],[4,8,10],[4,11,12],[9,13,14],[8,11,14],[10,12,14]],
           'source_ex2':[[1,2,3],[1,4,5],[3,5,6],[1,6,7],[3,4,7],[4,6,8],[1,10,15],[2,13,14],[5,9,11],[7,12,16],[8,9,10],[11,12,13],[14,15,16],[8,11,14],[9,12,15],[10,13,16]]}
    for k,v in cands.items(): print(k, json.dumps(verify(v)))
