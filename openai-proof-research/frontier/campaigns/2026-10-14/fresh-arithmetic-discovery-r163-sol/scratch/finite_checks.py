"""Bounded exact sanity examples, not mathematical gates."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json, random
ROOT=Path(__file__).resolve().parents[1]
rng=random.Random(163)
J=4; delta=F(1,100000); perturb=F(1,10**10)
# Four triangles sharing one vertex, all original edges separately labelled.
for attempt in range(100):
    edges=[]
    for j in range(1,J+1):
        h=F(4*j); tau=delta*F(j,5)
        for label,u,v,a,b in [('a',0,2*j-1,F(-1),h),('b',2*j-1,2*j,F(1),h-2*tau),('c',2*j,0,F(0),h-1)]:
            a+=rng.randint(-99,99)*perturb; b+=rng.randint(-99,99)*perturb
            edges.append((f'{label}{j}',u,v,a,b))
    pts=[(-a,b) for _,_,_,a,b in edges]
    if len(set(x for x,y in pts))<len(pts):continue
    slopes=[(pts[j][1]-pts[i][1])/(pts[j][0]-pts[i][0]) for i,j in combinations(range(len(pts)),2)]
    if len(set(slopes))==len(slopes):break
else:raise AssertionError('bounded generic perturbation failed')
def forest(t):
    par=list(range(2*J+1)); out=[]
    def find(x):
        while par[x]!=x:x=par[x]
        return x
    for lab,u,v,a,b in sorted(edges,key=lambda e:(e[3]*t+e[4],e[0])):
        u=find(u);v=find(v)
        if u!=v:par[u]=v;out.append(lab)
    return frozenset(out)
critical=[]
for j in range(J):
    a,b,c=edges[3*j:3*j+3]
    t=(b[4]-a[4])/(a[3]-b[3]);assert 0<t<delta;critical.append(t)
    assert c[3]*t+c[4]<a[3]*t+a[4]
assert critical==sorted(critical)
times=[F(-1,100000),*[(a+b)/2 for a,b in zip([F(0),*critical],critical+[delta])],2*delta]
forests=[forest(t) for t in times]
active=set().union(*(a^b for a,b in zip(forests,forests[1:])))
assert len(active)==8
initial=forest(F(-1,100000));final=forest(2*delta)
assert initial==frozenset([f'b{j}' for j in range(1,J+1)]+[f'c{j}' for j in range(1,J+1)])
assert final==frozenset([f'a{j}' for j in range(1,J+1)]+[f'c{j}' for j in range(1,J+1)])
def is_tree(labels):
    par=list(range(2*J+1))
    def find(x):
        while par[x]!=x:x=par[x]
        return x
    for lab,u,v,a,b in edges:
        if lab in labels:
            x,y=find(u),find(v)
            if x==y:return False
            par[x]=y
    return len(labels)==2*J and len({find(i) for i in range(2*J+1)})==1
exchange=[]
for i in range(1,J+1):
    for j in range(1,J+1):
        if is_tree(initial-{f'b{i}'}|{f'a{j}'}) and is_tree(final-{f'a{j}'}|{f'b{i}'}):exchange.append((i,j))
assert exchange==[(i,i) for i in range(1,J+1)]
# B=(-2,2)x(0,17) contains ALL points, no exchange crosses its boundary.
assert all(-2<x<2 and 0<y<17 for x,y in pts)
# Four active groups have gaps >3 in their vertical coordinate; a horizontal
# strip of half-width <1 can meet at most one group. Three miss one group.
ys=[sorted(y for lab,u,v,a,y in edges[3*j:3*j+3] if lab[0]!='c') for j in range(J)]
assert all(ys[j+1][0]-ys[j][1]>3 for j in range(J-1))
record={'kind':'finite sanity only','vertices':2*J+1,'original_edges':len(edges),'active_edges':sorted(active),'mutual_exchange_pairs':exchange,'distinct_sample_forests':len(set(forests)),'generic_dual_points':True,'all_dual_points_inside_B':True,'boundary_transfers':0,'coefficient_records':[[lab,u,v,str(a),str(b)] for lab,u,v,a,b in edges],'critical_times':[str(t) for t in critical]}
(ROOT/'private/finite-check-results.json').write_text(json.dumps(record,indent=2)+'\n')
print('Exact 9-vertex/12-edge example: 8 active labels; 4 mutual-exchange pairs; 0 boundary transfers; 5 forests.')
