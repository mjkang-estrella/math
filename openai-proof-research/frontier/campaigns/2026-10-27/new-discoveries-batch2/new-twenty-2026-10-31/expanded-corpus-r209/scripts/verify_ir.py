# Independent plain-set verification of the IR-graph of a given graph (edge list JSON).
import sys,json,itertools
E=json.loads(sys.argv[1]); n=1+max(max(e) for e in E)
V=range(n); nbr={v:set() for v in V}
for a,b in E: nbr[a].add(b); nbr[b].add(a)
def closed(v): return nbr[v]|{v}
def private(v,D):
    others=set()
    for u in D:
        if u!=v: others|=closed(u)
    return closed(v)-others
def irredundant(D): return all(private(v,D) for v in D)
irr=[set(D) for k in range(n+1) for D in itertools.combinations(V,k) if irredundant(D)]
IR=max(len(D) for D in irr)
S=[frozenset(D) for D in irr if len(D)==IR]
adjIR={A:set() for A in S}
for A in S:
    for B in S:
        if len(A-B)==1 and len(B-A)==1:
            (a,),(b,)=tuple(A-B),tuple(B-A)
            if b in nbr[a]: adjIR[A].add(B)
m=len(S); edges=sum(len(x) for x in adjIR.values())//2
degs=sorted(len(adjIR[A]) for A in S)
# walk the path from an endpoint
ends=[A for A in S if len(adjIR[A])==1]
walk=[]
if ends:
    prev=None;cur=ends[0]
    while True:
        walk.append(sorted(cur)); nxt=[B for B in adjIR[cur] if B!=prev]
        if not nxt: break
        prev,cur=cur,nxt[0]
print(json.dumps({'n':n,'edges_G':len(E),'IR':IR,'num_IR_sets':m,'IR_graph_edges':edges,'degree_multiset':degs,'is_path':edges==m-1 and len(walk)==m and max(degs)<=2,'walk':walk,'num_irredundant_sets':len(irr)}))
