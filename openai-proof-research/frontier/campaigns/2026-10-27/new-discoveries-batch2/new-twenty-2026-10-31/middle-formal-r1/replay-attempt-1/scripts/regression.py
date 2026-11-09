"""Independent literal set-based regression; no proof-generation dependencies."""
import itertools, json
from pathlib import Path
L=Path(__file__).resolve().parent.parent
E=[(0,1),(0,6),(1,6),(2,3),(2,7),(3,7),(4,6),(4,7),(5,6),(5,7),(6,7)]
V=[('v',i) for i in range(8)]
EN=[('e',a,b) for a,b in E]
def graph(nodes, relation):
    return {v:{w for w in nodes if w!=v and relation(v,w)} for v in nodes}
g={i:{b if a==i else a for a,b in E if i in (a,b)} for i in range(8)}
def rel(x,y):
    if x[0]==y[0]=='v': return False
    if x[0]==y[0]=='e': return bool(set(x[1:])&set(y[1:]))
    if x[0]=='e': x,y=y,x
    return x[1] in y[1:]
m=graph(V+EN,rel)
def connected(g,R,empty):
    if not R:return empty
    seen={next(iter(R))}
    while True:
        more=seen|set().union(*(g[v]&R for v in seen))
        if more==seen:return seen==R
        seen=more
def dom(g,S):return all(v in S or bool(g[v]&S) for v in g)
def feasible(g,S,empty):return dom(g,S) and connected(g,set(g)-S,empty)
def search(g,empty,cap):
    for k in range(cap+1):
        found=[list(s) for s in itertools.combinations(g,k) if feasible(g,set(s),empty)]
        if found:return k,len(found)
    return None
out={}
for empty in (True,False):
    out[str(empty)]={'G8':search(g,empty,4),'middle':search(m,empty,4)}
    assert out[str(empty)]=={'G8':(4,8),'middle':(4,2)}
assert connected(g,set(g),False)
assert feasible(g,{0,2,4,5},False)
assert feasible(m,{('e',0,1),('e',2,3),('e',4,6),('e',5,7)},False)
assert not rel(('v',0),('v',1))
assert not connected(g,{0,2,4,5},False)
out['edgeless_A']=search({0:set(),1:set()},True,2)
out['edgeless_B']=search({0:set(),1:set()},False,2)
out['middle_nodes']=len(m)
out['middle_edges']=sum(map(len,m.values()))//2
(L/'regression.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
