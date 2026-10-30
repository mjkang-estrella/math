"""Independent direct connected-support enumeration; no candidate imports/replays.
For a fixed terminal mask, inspect every connected vertex superset, retaining
all smallest supports. Each such support admits a spanning tree with |V|-1
edges; conversely every optimal tree gives such a support. Thus this exactly
tests the universal ALL-minimum-trees quantifier, including tied supports.
"""
from pathlib import Path
from itertools import combinations, product
import json,time
P=Path(__file__).resolve().parent
def graph(sizes):
    classes=[];v=0
    for n in sizes:classes.append(list(range(v,v+n)));v+=n
    edges=[];proj=[i for i,n in enumerate(sizes) for _ in range(n)]
    for i,j,L in [(0,1,2),(0,2,2),(0,3,2),(1,2,3),(1,3,3),(2,3,3)]:
        chain=[classes[i]]
        for _ in range(L-1):chain.append([v]);proj.append(4+v-sum(sizes));v+=1
        chain.append(classes[j])
        for a,b in zip(chain,chain[1:]):edges.extend(product(a,b))
    adj=[0]*v
    for a,b in edges:adj[a]|=1<<b;adj[b]|=1<<a
    return adj,classes,edges,proj
def connected(mask,adj):
    seen=0;front=mask&-mask
    while front:
        seen|=front;nxt=0
        while front:
            z=front&-front;front-=z;nxt|=adj[z.bit_length()-1]
        front=nxt&mask&~seen
    return seen==mask
def support_table(adj):
    return [(x,x.bit_count()) for x in range(1,1<<len(adj)) if connected(x,adj)]
def optimum(B,table):
    best=100;U=0;ties=0
    for x,c in table:
        if x&B==B:
            if c<best:best=c;U=x;ties=1
            elif c==best:U|=x;ties+=1
    return best-1,U,ties
def exact_sgp(adj,k,table):
    forbidden=set();ties=0
    for t in combinations(range(len(adj)),k):
        B=sum(1<<v for v in t);d,U,c=optimum(B,table);ties+=c>1
        for w in range(len(adj)):
            if U>>w&1 and not B>>w&1:forbidden.add(B|1<<w)
    bad=list(forbidden)
    for size in range(len(adj),k-1,-1):
        for t in combinations(range(len(adj)),size):
            S=sum(1<<v for v in t)
            if not any(S&f==f for f in bad):return {'maximum':size,'witness':t,'forbidden':len(bad),'terminal_sets_with_tied_supports':ties}
start=time.monotonic();R={}
base,C,E,pr=graph([1]*4);tb=support_table(base)
R['base']={str(k):exact_sgp(base,k,tb) for k in [2,3]}
assert R['base']['2']['maximum']==R['base']['3']['maximum']==5
# Exhaust every connected support on the m=2 blow-up, seeking shorter
# trees or a center choice absent from the union of optimal supports.
a,C,E,pr=graph([2]*4);tb=support_table(a);rim=[]
for t in product(*C[1:]):
    d,U,ties=optimum(sum(1<<v for v in t),tb)
    assert d==6 and all(U>>w&1 for w in C[0]);rim.append({'terminals':t,'distance':d,'optimal_supports':ties})
R['m2']={'order':len(a),'connected_supports_enumerated':len(tb),'rim_tests':rim}
# Verify ALL chosen class quadruples are forbidden, by exact all-support oracle.
R['m2']['forbidden_class_quadruples']=len(rim)*len(C[0])
# m10 GP falsifier: distances via repeated boolean-frontier BFS, independently
# assembled graph. Triple equality is precisely shortest-path betweenness.
a,C,E,pr=graph([10]*4);D=[]
for s in range(len(a)):
    row=[999]*len(a);row[s]=0;q=[s]
    for u in q:
        for v in range(len(a)):
            if a[u]>>v&1 and row[v]==999:row[v]=row[u]+1;q.append(v)
    D.append(row)
sel=sum(C,[]);nt=0
for u,v,w in combinations(sel,3):
    ds=sorted([D[u][v],D[u][w],D[v][w]])
    assert ds[0]+ds[1]>ds[2];nt+=1
R['m10']={'order':len(a),'edges':len(E),'GP_triples_tested':nt}
# Direct enumerate every support in the six-vertex lexicographic product.
a=[0]*6
for u,v in combinations(range(6),2):
    if u//2==v//2 or abs(u//2-v//2)==1:a[u]|=1<<v;a[v]|=1<<u
tb=support_table(a);R['lexicographic']=exact_sgp(a,4,tb)
assert R['lexicographic']['maximum']==5
B=sum(1<<v for v in [0,1,4,5]);d,U,t=optimum(B,tb)
R['lexicographic']['outer_terminals']={'distance':d,'union_optimal_supports_mask':U,'ties':t}
assert d==4 and U==63 and t==2
# Exact [2:3] simultaneous condition on P3.
p3=[2,5,2];tb=support_table(p3)
R['p3']={str(k):exact_sgp(p3,k,tb) for k in [2,3]}
R['wall_seconds']=time.monotonic()-start
(P/'independent-evidence.json').write_text(json.dumps(R,indent=2))
print(json.dumps(R,indent=2))
