"""Finite diagnostics for I22. These do not replace the report's proofs."""
from pathlib import Path
from fractions import Fraction as Q
from itertools import combinations, product
from collections import defaultdict
import json, math, random

ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT/'frontier/experiments/i22_combinatorial_discovery/results.json'

def binary_rank(cols):
    basis = {}
    for v in cols:
        while v:
            b = v.bit_length()-1
            if b in basis: v ^= basis[b]
            else:
                basis[b] = v
                break
    return len(basis)

def density_checks():
    rng = random.Random(2209)
    count = 0
    # Loops and repeated columns are allowed. Kappa is varied to test ties;
    # the report uses the source's fixed kappa=2**100.
    for n in range(1, 8):
        full = (1<<n)-1
        for rep in range(8):
            cols = [rng.randrange(16) for _ in range(n)]
            ranks = [binary_rank([cols[i] for i in range(n) if a>>i&1]) for a in range(full+1)]
            def closure(a):
                return sum(1<<i for i in range(n) if ranks[a|1<<i] == ranks[a])
            flats = [a for a in range(full+1) if closure(a)==a]
            for kappa in (1, 2, 3, 2**100):
                for _ in range(12):
                    base = closure(rng.randrange(full+1))
                    sample = rng.randrange(full+1)
                    feasible = [a for a in range(full+1) if a&base==base]
                    primary = lambda a: kappa*ranks[a]-(a&sample).bit_count()
                    optimal = min(primary(a) for a in flats if a&base==base)
                    max_flats = [a for a in flats if a&base==base and primary(a)==optimal]
                    union = 0
                    for a in max_flats: union |= a
                    objective = lambda a: (n+1)*primary(a)-a.bit_count()
                    low = min(map(objective, feasible))
                    minimizers = [a for a in feasible if objective(a)==low]
                    assert minimizers == [union]
                    assert union in flats
                    for z in range(full+1):
                        lhs = ((closure(union|z)^union)&sample).bit_count()
                        assert lhs <= kappa*(ranks[union|z]-ranks[union])
                    count += 1
    return count

def matchings(vertices, edges):
    vertices = frozenset(vertices)
    if not vertices:
        yield frozenset()
        return
    v = min(vertices)
    for e,(a,b) in edges.items():
        if a==v and b in vertices: w=b
        elif b==v and a in vertices: w=a
        else: continue
        for rest in matchings(vertices-{v,w}, edges):
            yield rest|{e}

def entropy(values):
    return -sum(float(p)*math.log(float(p)) for p in values if p)

def klee_checks():
    edges = {i:(0,1) for i in range(3)}
    colors = {i:i for i in range(3)}
    vertices = {0,1}
    cuts=[]
    records=[]
    for m in range(1,8):
        ms=list(matchings(vertices,edges))
        good=[M for M in ms if all(sum((a in S)!=(b in S) for e,(a,b) in edges.items() if e in M)==1 for S in cuts)]
        assert len(good)==3
        assert {frozenset(e for e in edges if colors[e]==c) for c in range(3)}==set(good)
        assert len(edges)==3*m
        for M in good: assert len(M)==m
        records.append({'m':m,'all_matchings':len(ms),'face_matchings':len(good)})
        v=min(vertices); inc=[e for e,p in edges.items() if v in p];assert len(inc)==3
        new=list(range(max(vertices)+1,max(vertices)+4))
        for S in cuts:
            if v in S: S.remove(v);S.update(new)
        vertices.remove(v);vertices.update(new)
        for i,e in enumerate(inc):
            a,b=edges[e];edges[e]=(new[i],b if a==v else a)
        eid=max(edges)+1
        for i,e in enumerate(inc):
            edges[eid+i]=(new[(i+1)%3],new[(i+2)%3]);colors[eid+i]=colors[e]
        cuts.append(set(new))
    return records

def scalar_checks():
    c=math.log(3)/(2*math.log(1.5))
    total=0; worst=-1
    for a in range(181):
        for b in range(181-a):
            p=[Q(a,180),Q(b,180),Q(180-a-b,180)]
            F=entropy(p);B=entropy(1-z for z in p)
            assert F <= c*B+2e-14
            worst=max(worst,F-c*B);total+=1
    edges=dict(enumerate(e for e in combinations(range(6),2) if e not in [(0,1),(2,3),(4,5)]))
    ms=list(matchings(range(6),edges));assert len(ms)==8
    assert all(sum(e in M for M in ms)==2 for e in edges)
    assert 3**9>4**7
    return {'triples':total,'coefficient':c,'max_numerical_defect':worst,'degree_four_example_matchings':len(ms)}

def gluing_checks():
    records=[]
    for n in (6,8,10):
        vertices=set(range(n));S=set(range(3 if n<10 else 5))
        edges=dict(enumerate(combinations(range(n),2)))
        cross={e for e,(a,b) in edges.items() if (a in S)!=(b in S)}
        left={e for e,(a,b) in edges.items() if a in S and b in S}
        right=set(edges)-cross-left
        all_ms=list(matchings(vertices,edges));ms=[M for M in all_ms if len(M&cross)==1]
        weights={e:1+(e*7+3)%5 for e in edges}
        w={M:math.prod(weights[e] for e in M) for M in ms};Z=sum(w.values());law={M:Q(v,Z) for M,v in w.items()}
        p1=defaultdict(Q);p2=defaultdict(Q);q=defaultdict(Q)
        for M,p in law.items():
            p1[M&(left|cross)]+=p;p2[M&(right|cross)]+=p;q[next(iter(M&cross))]+=p
        for M,p in law.items():
            e=next(iter(M&cross));assert p==p1[M&(left|cross)]*p2[M&(right|cross)]/q[e]
        err=abs(entropy(law.values())-entropy(p1.values())-entropy(p2.values())+entropy(q.values()))
        assert err<1e-12
        # Positive Gibbs laws with a dyadic cut penalty: conditioning a nearly
        # tight cut, exact parity slack, total variation, and coordinate change.
        for k in (1,2,4,8):
            w={M:Q(1,2**(k*len(M&cross))) for M in all_ms};Z=sum(w.values());p={M:v/Z for M,v in w.items()}
            bad=sum(v for M,v in p.items() if len(M&cross)>1)
            delta=sum(v*len(M&cross) for M,v in p.items())-1
            assert 2*bad<=delta
            cond={M:(v/(1-bad) if len(M&cross)==1 else Q(0)) for M,v in p.items()}
            tv=sum(abs(p[M]-cond[M]) for M in all_ms)/2;assert tv==bad
            for e in edges:
                assert abs(sum(p[M]-cond[M] for M in all_ms if e in M))<=bad
        records.append({'n':n,'all_matchings':len(all_ms),'crossing_one':len(ms),'entropy_identity_error':err})
    return records

def palette_checks():
    rows=[]
    for k in range(2,22):
        edges=[]
        for v in range(3):edges.extend([((v,i),(v+1,i)) for i in range(k)])
        edges.extend([((3,i),(0,(i+1)%k)) for i in range(k)])
        seen={(0,0)};change=True
        while change:
            change=False
            for a,b in edges:
                if (a in seen)!=(b in seen):seen.update((a,b));change=True
        assert len(seen)==4*k
        # Coloring enumeration is only needed for the smallest cases.
        if k<=5:
            valid=[x for x in product(range(k),repeat=4) if all(not(x[a[0]]==a[1] and x[b[0]]==b[1]) for a,b in edges)]
            assert (len(valid)==0)==(k==2)
            rows.append({'k':k,'cover_vertices':len(seen),'colorings':len(valid)})
    return {'connected_covers':20,'small_colorings':rows}

def main():
    result={'density_instances':density_checks(),'klee':klee_checks(),'scalar':scalar_checks(),'gluing':gluing_checks(),'palette':palette_checks()}
    OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,sort_keys=True))

if __name__=='__main__':main()
