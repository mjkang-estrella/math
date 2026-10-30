"""Bounded independent formulations; no finite-to-universal inference."""
import itertools,json

def partitions(v):
    if not v:
        yield ()
        return
    a,*rest=v
    for bc in itertools.combinations(rest,2):
        for p in partitions([x for x in rest if x not in bc]):
            yield ((a,)+bc,)+p

def matchings(v):
    if not v:
        yield ()
        return
    a,*rest=v
    yield from matchings(rest)
    for b in rest:
        for m in matchings([x for x in rest if x!=b]):
            yield ((a,b),)+m

def main():
    n=6; edges=list(itertools.combinations(range(n),2)); ix={e:i for i,e in enumerate(edges)}
    bit=lambda es:sum(1<<ix[tuple(sorted(e))] for e in es)
    parts=list(partitions(list(range(n))))
    ts=[tuple(bit(itertools.combinations(t,2)) for t in p) for p in parts]
    factors=[a|b for a,b in ts]
    ms=[bit(m) for m in matchings(list(range(n)))]
    has=lambda g:any(g&f==f for f in factors)
    classes={};robust=0;positive=0
    for g in range(1<<len(edges)):
        wedge=any(all((g&t).bit_count()>=2 for t in pp) for pp in ts)
        # Actual positive neighbors, using additions only after monotonicity.
        pos=any(has(g|m) for m in ms if not g&m)
        assert wedge==pos
        # Two independent negative formulations: actual neighbor and hitting all factors.
        present=[f for f in factors if g&f==f]
        blocker=any(all(m&f for f in present) for m in ms if m&g==m)
        neg=any(not has(g^m) for m in ms if m&g==m)
        assert blocker==neg
        assert pos or neg
        key=f'positive={pos},negative={neg}'
        classes[key]=classes.get(key,0)+1
        positive+=bool(present);robust+=not neg
    h=bit([(0,1),(0,2),(1,2),(0,3),(0,4),(3,4),(0,5),(1,5),(3,5)])
    g=h|bit([(4,5)])
    triangles=[bit(t) for t in itertools.combinations(edges,3) if len(set(sum((list(e) for e in t),[])))==3]
    covered=set()
    for t in itertools.combinations(range(6),3):
        z=bit(itertools.combinations(t,2))
        if h&z==z:covered.update(t)
    assert has(g) and not has(h) and covered==set(range(6))
    # Greedy wedge-factor failure on a spanning path, despite existence of a factor.
    path=bit([(i,i+1) for i in range(5)])
    assert any(all((path&t).bit_count()>=2 for t in p) for p in ts)
    assert not any((path&bit(itertools.combinations(t,2))).bit_count()>=2 for t in [(0,4,5)])
    return dict(graphs=32768,partitions=len(parts),matchings=len(ms),classes=classes,
                original_triangle_factor_graphs=positive,robust_positive_graphs=robust,
                local_triangle_test_countermodel=dict(G=g,H=h,deleted=[[4,5]]),
                status='PASS; diagnostics only')

if __name__=='__main__':print(json.dumps(main(),sort_keys=True,indent=2))
