import itertools,sys,json
V=range(9); parts=[{0,1,2},{3,4,5},{6,7,8}]
E={frozenset((a,b)) for a in V for b in V if a<b and not any(a in p and b in p for p in parts)}
for e in ['05','08','14','23','26','37','56']: E.discard(frozenset((int(e[0]),int(e[1]))))
adj={v:{u for u in V if frozenset((u,v)) in E} for v in V}
N=lambda v: adj[v]|{v}
def irr(S):
    for v in S:
        others=set().union(*[N(u) for u in S if u!=v]) if len(S)>1 else set()
        if not (N(v)-others): return False
    return True
mx=max(k for k in range(10) if any(irr(S) for S in itertools.combinations(V,k)))
IR=[frozenset(S) for S in itertools.combinations(V,mx) if irr(S)]
edges=[]
for X,Y in itertools.combinations(IR,2):
    D=X^Y
    if len(D)==2:
        x,=X-Y; y,=Y-X
        if y in adj[x]: edges.append((sorted(X),sorted(Y)))
deg={X:0 for X in IR}
for a,b in edges: deg[frozenset(a)]+=1; deg[frozenset(b)]+=1
# connectivity
import collections
g=collections.defaultdict(set)
for a,b in edges: g[frozenset(a)].add(frozenset(b)); g[frozenset(b)].add(frozenset(a))
seen={IR[0]}; st=[IR[0]]
while st:
    x=st.pop()
    for y in g[x]:
        if y not in seen: seen.add(y); st.append(y)
connected = len(seen)==len(IR)
Gconn=True; s={0}; st=[0]
while st:
    x=st.pop()
    for y in adj[x]:
        if y not in s: s.add(y); st.append(y)
out={'edges_G':len(E),'G_connected':len(s)==9,'IR':mx,'num_IR_sets':len(IR),'IR_sets':[sorted(X) for X in IR],'IR_graph_edges':len(edges),'degrees':sorted(deg.values()),'IR_graph_connected':connected,'is_path':connected and len(edges)==len(IR)-1 and max(deg.values())<=2}
print(json.dumps({k:v for k,v in out.items() if k!='IR_sets'}))
print(out['IR_sets'])
json.dump(out,open(sys.argv[1],'w'),indent=1)
