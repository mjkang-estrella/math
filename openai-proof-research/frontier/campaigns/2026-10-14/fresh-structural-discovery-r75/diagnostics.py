#!/usr/bin/env python3
"""Finite implementation diagnostics only; no verification of the full source compiler."""
import itertools,json,math

def build(n,edges,sorts,station_count=None):
    s=1+max(sorts) if sorts else 1
    m=max(2,math.isqrt(s-1)+1) if station_count is None else station_count
    assert m*m>=s
    adj={};cell={};target={}
    def vertex(v,c,d):adj[v]=set();cell[v]=c;target[v]=d
    def edge(v,w):assert v!=w and w not in adj[v];adj[v].add(w);adj[w].add(v)
    def trans(v,i):
        x,y=divmod(v,m)
        return (((x+2*y+(i==1))%m)*m+y) if i<2 else x*m+(y+2*x+(i==3))%m
    for v in range(m*m):vertex(('q',v),v,101 if v==0 else 100)
    for v in range(n):vertex(('y',v),sorts[v],20);edge(('y',v),('q',sorts[v]))
    for v,w in edges:edge(('y',v),('y',w))
    arcs=[]
    for v in range(m*m):
        for i in range(4):
            a=('a',v,i);b=('b',v,i);w=trans(v,i);arcs.append((v,w))
            vertex(a,v,30+2*i);vertex(b,v,31+2*i)
            edge(('q',v),a);edge(a,b);edge(b,('q',w))
    for v in list(adj):
        deficit=target[v]-len(adj[v]);assert deficit>=0
        for j in range(deficit):
            l=('leaf',v,j);vertex(l,cell[v],1);edge(v,l)
    assert all(len(adj[v])==target[v] for v in adj)
    assert max(map(len,adj.values()))==101
    assert [v for v in adj if len(adj[v])==101]==[('q',0)]
    assert max(sum(c==i for c in cell.values()) for i in range(m*m))<=2048
    return adj,cell,arcs,m

def stable_colors(adj):
    vs=list(adj);cols={v:len(adj[v]) for v in vs}
    for t in range(len(vs)):
        sig={v:(cols[v],tuple(sorted(cols[w] for w in adj[v]))) for v in vs}
        names={x:i for i,x in enumerate(sorted(set(sig.values())))}
        nc={v:names[sig[v]] for v in vs}
        if len(set(nc.values()))==len(set(cols.values())):return nc,t+1
        cols=nc
    raise AssertionError('no stabilization')

def main():
    rows=[];cuts=0;lifts=0
    for m in range(2,7):
        n=m*m;edges={(i,i+1) for i in range(n-1)}
        a,c,arcs,m=build(n,edges,list(range(n)),m)
        colors,rounds=stable_colors(a)
        assert len({colors[('q',i)] for i in range(m*m)})==m*m
        assert len({colors[('y',i)] for i in range(n)})==n
        for i in range(m*m):
            for j in range(4):
                assert len([v for v in a[('q',i)] if len(a[v])==30+2*j])==1
                assert len([v for v in a[('q',i)] if len(a[v])==31+2*j])==1
        if m<=3:
            for bits in range(1,1<<(m*m)):
                S={i for i in range(m*m) if bits>>i&1}
                if len(S)>m*m/2:continue
                boundary=sum((v in S)!=(w in S) for v,w in arcs)
                assert 5*boundary>=2*len(S);cuts+=1
        rows.append(dict(frame_side=m,vertices=len(a),stations=m*m,recognition_rounds=rounds))
    # Every dihedral automorphism of a monochromatic cycle: whole fixed-frame lift.
    for n in range(3,9):
        edges={tuple(sorted((i,(i+1)%n))) for i in range(n)}
        a,c,arcs,m=build(n,edges,[0]*n)
        for sign in [-1,1]:
            for shift in range(n):
                def f(v):
                    if v[0]=='y':return ('y',(sign*v[1]+shift)%n)
                    if v[0]=='leaf':return ('leaf',f(v[1]),v[2])
                    return v
                assert len({f(v) for v in a})==len(a)
                assert all({f(w) for w in a[v]}==a[f(v)] for v in a)
                lifts+=1
    print(json.dumps(dict(status='PASS',frame_cases=rows,exact_base_cuts=cuts,whole_graph_offset_lifts=lifts,limits='Finite construction/recognition and automorphism checks only. No full-output exhaustive cuts, k-WL game computation, or source computation compiler replay.'),indent=2))
if __name__=='__main__':main()
