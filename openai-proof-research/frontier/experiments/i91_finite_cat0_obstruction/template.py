"""Actual A template, canonical string ordering; stdlib only, no file writes."""
from itertools import combinations, product
from collections import deque

def template():
    points=range(1,8)
    lines=sorted({tuple(sorted((i,j,i^j))) for i,j in combinations(points,2)})
    lname={l:'L'+''.join(map(str,l)) for l in lines}
    vertices=sorted(['X'+str(i) for i in points]+['Y'+str(i) for i in (1,2,4,7)]+list(lname.values()))
    edges=[]
    for i in points:
        for kind in ('X','Y'):
            if kind=='Y' and i not in (1,2,4,7):continue
            for l in lines:
                if i not in l or (kind=='Y' and i==7 and 4 in l):continue
                edges.append(tuple(sorted((kind+str(i),lname[l]))))
    edges=sorted(edges); adj={v:set() for v in vertices}
    for u,v in edges:adj[u].add(v);adj[v].add(u)
    hexagons=[]
    for i,j,k in combinations(points,3):
        if i^j==k:continue
        ij=lname[tuple(sorted((i,j,i^j)))];jk=lname[tuple(sorted((j,k,j^k)))];ki=lname[tuple(sorted((k,i,k^i)))]
        for reps in product(*[('X'+str(t),'Y'+str(t)) if t in (1,2,4,7) else ('X'+str(t),) for t in (i,j,k)]):
            cyc=(reps[0],ij,reps[1],jk,reps[2],ki)
            if all(cyc[(n+1)%6] in adj[cyc[n]] for n in range(6)):hexagons.append(cyc)
    hexagons=sorted(hexagons)
    opp=[{tuple(sorted((h[i],h[i+3]))) for i in range(3)} for h in hexagons]
    graph=[{j for j in range(len(opp)) if i!=j and opp[i]&opp[j]} for i in range(len(opp))]
    diam=0
    for root in range(len(graph)):
        ds={root:0};q=deque([root])
        while q:
            u=q.popleft()
            for v in sorted(graph[u]):
                if v not in ds:ds[v]=ds[u]+1;q.append(v)
        assert len(ds)==len(graph)
        diam=max(diam,max(ds.values()))
    return {'vertices':vertices,'edges':edges,'adj':adj,'lines':lines,'lname':lname,'hexagons':hexagons,'opposites':opp,'hexagon_diameter':diam}

def line(i,j):return 'L'+''.join(map(str,sorted((i,j,i^j))))

if __name__=='__main__':
    import json
    t=template()
    print(json.dumps({'vertices':len(t['vertices']),'edges':len(t['edges']), 'decorations':sum(len(a)*(len(a)-1)//2 for a in t['adj'].values()),'hexagons':len(t['hexagons']),'hexagon_diameter':t['hexagon_diameter']},sort_keys=True))
