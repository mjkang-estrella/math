# Independent check of MathDB 355701 witness using the SOURCE definitions literally
# (Bishop-Kuss-Peet 2208.06912 Sec 2.3, Def 4.1 triangle via points, Def 4.2 line 2-coloring).
import itertools, json, sys
L=[{0,2,3},{2,4,5},{3,5,8},{2,7,8},{1,3,6},{0,6,8},{0,1,4},{4,6,7},{1,5,7}]
P=range(9)
out={}
# configuration axioms
out['lines_distinct']=len({frozenset(l) for l in L})==9
out['line_sizes']=[len(l) for l in L]
out['point_degrees']=[sum(p in l for l in L) for p in P]
out['max_lines_through_pair']=max(sum(a in l and b in l for l in L) for a,b in itertools.combinations(P,2))
# connectivity of Levi graph
seen={0}; stack=[0]
while stack:
    p=stack.pop()
    for l in L:
        if p in l:
            for q in l:
                if q not in seen: seen.add(q); stack.append(q)
out['connected']=len(seen)==9
# triangles by the source point definition: ordered points p1,p2,p3 and lines l1,l2,l3
tri=set()
for p1,p2,p3 in itertools.permutations(P,3):
    for i1,i2,i3 in itertools.product(range(9),repeat=3):
        l1,l2,l3=L[i1],L[i2],L[i3]
        if p1 in l1 and p2 in l1 and p3 not in l1 and p2 in l2 and p3 in l2 and p1 not in l2 and p1 in l3 and p3 in l3 and p2 not in l3:
            tri.add((frozenset((p1,p2,p3)),frozenset((i1,i2,i3))))
tri_pts={t[0] for t in tri}
out['n_triangles_point_sets']=len(tri_pts)
out['n_triangles_line_sets']=len({t[1] for t in tri})
# the source says lines determined by points; check bijection
out['bijection_points_lines']=len(tri)==len(tri_pts)==len({t[1] for t in tri})
trilines=sorted(sorted(t[1]) for t in tri)
# alternative characterisation: 3 lines pairwise meeting in 3 distinct points (GAP code criterion)
alt=[]
for c in itertools.combinations(range(9),3):
    a,b,d=(L[i] for i in c)
    if len((a&b)|(a&d)|(b&d))==3 and all(len(x)==1 for x in (a&b,a&d,b&d)): alt.append(sorted(c))
out['gap_criterion_matches']=sorted(alt)==trilines
# min monochromatic triangles over all 2^9 line colourings
counts=[]
for mask in range(512):
    col=[(mask>>i)&1 for i in range(9)]
    counts.append(sum(1 for t in trilines if col[t[0]]==col[t[1]]==col[t[2]]))
out['min_mono']=min(counts); out['n_colorings_achieving_min']=counts.count(min(counts))
# mutually intersecting sets (pairwise nonempty intersection)
def mi(S): return all(L[i]&L[j] for i,j in itertools.combinations(S,2))
sets=[S for k in range(10) for S in itertools.combinations(range(9),k) if mi(S)]
out['max_mutually_intersecting']=max(len(S) for S in sets)
incl_max=[S for S in sets if not any(set(S)<set(T) for T in sets)]
out['inclusion_maximal_sizes']=sorted({len(S) for S in incl_max})
out['n_maximum_sets']=sum(len(S)==out['max_mutually_intersecting'] for S in sets)
out['S0123_mutually_intersecting']=mi((0,1,2,3))
# general-position variant (pairwise intersecting, no three concurrent) for robustness
def gp(S): return mi(S) and all(not (L[i]&L[j]&L[k]) for i,j,k in itertools.combinations(S,3))
out['max_general_position_intersecting']=max(len(S) for k in range(10) for S in itertools.combinations(range(9),k) if gp(S))
# automorphisms (point permutations preserving line set)
LS={frozenset(l) for l in L}
aut=sum(1 for p in itertools.permutations(P) if {frozenset(p[x] for x in l) for l in L}==LS)
out['aut_order']=aut
# Pappus-type invariant: is there a partition of lines into 3 parallel classes?
par=[(i,j) for i,j in itertools.combinations(range(9),2) if not L[i]&L[j]]
out['n_parallel_pairs']=len(par)
print(json.dumps(out,indent=1))
json.dump(out,open('checks/v3-independent.json','w'),indent=1)
