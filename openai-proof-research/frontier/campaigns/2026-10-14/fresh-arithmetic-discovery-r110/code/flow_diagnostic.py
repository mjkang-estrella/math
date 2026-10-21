"""Finite diagnostics for the quotient correction graph, not the source theorem."""
from collections import defaultdict, deque
from itertools import product
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parents[1]

def add(a,b,sign=1):
    c=dict(a)
    for e,v in b.items():
        c[e]=c.get(e,0)+sign*v
        if c[e]==0:del c[e]
    return c

def val(a):return min(a) if a else float('inf')

def test(n):
    words=[''.join(x) for x in product('12',repeat=n)]
    nodes=[(i,w) for i in range(11) for w in words]
    graph=defaultdict(list)
    for i,w in nodes:
        for offset in ([1,2] if w[0]=='1' else [3,4]):
            v=((i-offset)%11,w[1:]+w[0])
            graph[(i,w)].append(v);graph[v].append((i,w))
    seen=set(); components=0; edges=0
    for root in nodes:
        if root in seen:continue
        components+=1; parent={root:None};order=[];queue=deque([root]);seen.add(root)
        while queue:
            v=queue.popleft();order.append(v)
            for u in graph[v]:
                if u not in seen:seen.add(u);parent[u]=v;queue.append(u)
        orbit={root[1][j:]+root[1][:j] for j in range(n)}
        assert set(order)=={(i,w) for i in range(11) for w in orbit}
        errors={v:{((j*7)%13)-6:(j%5)+1} for j,v in enumerate(order[1:],1)}
        total={}
        for e in errors.values():total=add(total,e)
        errors[root]={k:-v for k,v in total.items()}
        lower=min(val(e) for e in errors.values())
        residual={v:dict(e) for v,e in errors.items()}; divergence={v:{} for v in order}
        for v in reversed(order[1:]):
            p=parent[v];flow=residual[v];edges+=1
            assert val(flow)>=lower
            divergence[v]=add(divergence[v],flow)
            divergence[p]=add(divergence[p],flow,-1)
            residual[p]=add(residual[p],flow)
        assert not residual[root]
        assert divergence==errors
    return {'length':n,'vertices':len(nodes),'rotation_components':components,'tree_edges':edges}

def main():
    graph=[test(n) for n in range(3,10)]
    inequalities=0
    for a,a0,b,c in product(range(4),repeat=4):
        B=3*(a+a0)+b+c; M=B+3*a+2*a0+b+c+1
        for h,f in product(range(13),repeat=2):
            if not ((h==0 and f>=3) or (h==1 and f>=2) or h>=2):continue
            delta=(2*h+f-3)*M-(h-1)*B-a*(h+f)-f*a0-b-c
            assert delta>=0
            inequalities+=1
    result={'graph_cases':graph,'valuation_inequalities':inequalities,
            'scope':'Finite scalar quotient-graph flow and arithmetic bound only; no spectral data, infinite correction, Artin approximation, effective field or full Kurosh theorem verified.'}
    (ROOT/'notes/diagnostics.json').write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
