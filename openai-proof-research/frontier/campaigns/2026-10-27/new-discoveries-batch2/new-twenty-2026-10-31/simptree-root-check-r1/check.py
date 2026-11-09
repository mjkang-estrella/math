import itertools,sys,json
F=[frozenset(int(c,16) for c in s) for s in "0123 1234 1235 1356 1456 1457 0147 0467 89AB".split()]
faces=set()
for f in F:
    for k in range(1,5):
        for s in itertools.combinations(sorted(f),k): faces.add(frozenset(s))
alpha=[sum(1 for s in faces if len(s)==k+1) for k in range(4)]
p=alpha[0]; n=3
from math import comb
conds={k:(alpha[k]==(p-n)*comb(n,k)+comb(n,k+1)) for k in range(1,n)}
# facet-ridge incidence graph: is it a forest? (no (2,3) circuits <=> bipartite incidence graph between facets and triangles acyclic)
tri={s for s in faces if len(s)==3}
nodes=[('F',i) for i in range(len(F))]+[('T',t) for t in tri]
edges=[(('F',i),('T',t)) for i,f in enumerate(F) for t in tri if t<=f]
par={x:x for x in nodes}
def find(x):
    while par[x]!=x: par[x]=par[par[x]]; x=par[x]
    return x
cyc=False
for a,b in edges:
    ra,rb=find(a),find(b)
    if ra==rb: cyc=True
    else: par[ra]=rb
# (2,3)-connectivity of facets: facets connected via shared triangles
fp={i:i for i in range(len(F))}
def ff(x):
    while fp[x]!=x: x=fp[x]
    return x
for i,j in itertools.combinations(range(len(F)),2):
    if len(F[i]&F[j])==3: fp[ff(i)]=ff(j)
comps=len({ff(i) for i in range(len(F))})
out={'alpha':alpha,'p':p,'alpha_n_eq_p_minus_n':alpha[3]==p-n,'intermediate_conditions':conds,'incidence_graph_has_cycle':cyc,'facet_ridge_components':comps}
print(json.dumps(out)); json.dump(out,open(sys.argv[1],'w'),indent=1)
