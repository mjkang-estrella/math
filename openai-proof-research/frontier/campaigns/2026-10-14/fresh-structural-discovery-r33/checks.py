#!/usr/bin/env python3
"""MIT. Exact bounded diagnostics; not a proof of the unresolved target."""
from fractions import Fraction
from itertools import combinations, permutations, product
from functools import lru_cache
import json

def balance(n, arcs):
    out=[0]*n; inc=[0]*n
    for u,v in arcs:
        assert u != v
        out[u]+=1; inc[v]+=1
    return [out[i]-inc[i] for i in range(n)]

def run():
    rows=[]
    assert Fraction(4,7)+Fraction(16,35)+Fraction(16,49)==Fraction(332,245)
    saving=Fraction(7,16)-Fraction(332,245*16)
    assert saving==Fraction(1383,3920) and saving>Fraction(1,3)
    for m in range(8,1001):
        assert m//2>=Fraction(7*m,16)
    rows.append({'test':'folding_constants','saving':str(saving),'rounding_cases':993})

    # Every shift pair is one Hamilton cycle; every resulting arc set is balanced.
    for m in range(2,21,2):
        N=2*m; n=2*N; all_edges=set(); arcs=set(); pieces=[]
        for i in range(m):
            edges={tuple(sorted((j,N+(j+s)%N))) for j in range(N) for s in (2*i,2*i+1)}
            assert len(edges)==n and not (edges & all_edges)
            all_edges |= edges
            adj=[set() for _ in range(n)]
            for u,v in edges: adj[u].add(v); adj[v].add(u)
            assert all(len(a)==2 for a in adj)
            seen={0}; todo=[0]
            while todo:
                for v in adj[todo.pop()]:
                    if v not in seen: seen.add(v); todo.append(v)
            assert len(seen)==n
            aa={(u,v) if i<m//2 else (v,u) for u,v in edges}
            assert not ({u for u,v in aa} & {v for u,v in aa})
            arcs |= aa; pieces.append(aa)
        assert len(all_edges)==N*N and len(arcs)==n*n//4
        assert balance(n,arcs)==[0]*n
        assert all(not ((v,u) in arcs) for u,v in arcs)
        rows.append({'test':'alternating_hamilton_pieces','m':m,'vertices':n,
                     'undirected_pieces':len(pieces),'directed_runs':len(arcs)})

    # All cut class-counts, not only random vertex cuts.
    count=0
    for t in range(1,11):
        for x in product(range(t+1),repeat=4):
            s=sum(x)
            out=sum(x[i]*(t-x[(i+1)%4]) for i in range(4))
            inc=sum((t-x[i])*x[(i+1)%4] for i in range(4))
            assert out==inc
            assert 2*out>=t*min(s,4*t-s)
            count+=1
        n=4*t
        cyc={(i*t+a,((i+1)%4)*t+b) for i in range(4) for a in range(t) for b in range(t)}
        extra={(i*t+a,((i+3)%4)*t+b) for i in (0,2) for a in range(t) for b in range(t)}
        pt=cyc|extra
        assert len(pt)==6*t*t
        assert balance(n,cyc)==[0]*n
        assert balance(n,pt)==[t if i//t in (0,2) else -t for i in range(n)]
        missing={(i*t+a,((i+3)%4)*t+b) for i in (1,3) for a in range(t) for b in range(t)}
        assert balance(n,pt|missing)==[0]*n
    rows.append({'test':'four_class_cut_and_excess','all_class_cuts':count,'t_max':10})

    # Every ordered loop/parallel class gets unique subdivision vertices.
    # Directed 6-cycle: identify pairs to create both loops and repeated arcs.
    arcs={(0,1),(1,2),(2,3),(3,4),(4,5),(5,0)}
    fibers={0:0,1:0,2:1,3:1,4:0,5:1}
    lifted=[]; seen=set(); nextv=2; added=0
    for u,v in sorted(arcs):
        a,b=fibers[u],fibers[v]
        if a==b or (a,b) in seen:
            lifted.extend([(a,nextv),(nextv,b)]); nextv+=1; added+=1
        else:
            lifted.append((a,b)); seen.add((a,b))
    assert len(lifted)==len(set(lifted)) and balance(nextv,set(lifted))==[0]*nextv
    assert any((v,u) in lifted for u,v in lifted) # Allowed antiparallel loop subdivision.
    rows.append({'test':'loop_parallel_subdivision','original_arcs':6,'added_vertices':added,
                 'simple':True,'balanced':True})

    # K4 symmetric digraph: enumerate every directed simple cycle, then exact cover DP.
    n=4; aa=[(u,v) for u in range(n) for v in range(n) if u!=v]; ix={e:i for i,e in enumerate(aa)}
    masks=set()
    for k in range(2,n+1):
        for vertices in combinations(range(n),k):
            for tail in permutations(vertices[1:]):
                cyc=(vertices[0],)+tail
                masks.add(sum(1<<ix[(cyc[i],cyc[(i+1)%k])] for i in range(k)))
    @lru_cache(None)
    def opt(mask):
        if not mask: return 0
        bit=mask & -mask
        return 1+min(opt(mask^c) for c in masks if c&bit and c&mask==c)
    assert opt((1<<12)-1)==4
    und=[(0,1,2,3),(0,1,3,2),(0,2,1,3)]
    counts={e:0 for e in combinations(range(4),2)}
    for cyc in und:
        for i in range(4): counts[tuple(sorted((cyc[i],cyc[(i+1)%4])))]+=1
    assert set(counts.values())=={2}
    rows.append({'test':'credited_K4_control','directed_cycle_number':4,'undirected_doubled_cycles':3,
                 'enumerated_directed_cycles':len(masks)})
    return {'status':'PASS_EXACT_BOUNDED_DIAGNOSTICS','checks':rows,
            'limitation':'Does not prove the full decomposition, routing, random-pairing lemma, or novelty.'}

if __name__=='__main__':
    print(json.dumps(run(),indent=2,sort_keys=True))
