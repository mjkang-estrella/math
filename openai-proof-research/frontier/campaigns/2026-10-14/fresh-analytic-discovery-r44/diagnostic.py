#!/usr/bin/env python3
"""MIT. Exact finite checks of counting interfaces; NOT proof of T221R."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
import json


def matchings(ports):
    ports = tuple(sorted(ports))
    if not ports:
        yield ()
        return
    x = ports[0]
    for j in range(1, len(ports)):
        y = ports[j]
        for tail in matchings(ports[1:j] + ports[j+1:]):
            yield tuple(sorted(((x, y),) + tail))


def count_sets(matching, degree, cavity_vertices, order):
    eligible = [e for e in matching if e[0]//degree != e[1]//degree
                and all(p//degree not in cavity_vertices for p in e)]
    return sum(len({p//degree for e in es for p in e}) == 2*order
               for es in combinations(eligible, order))


def bond(n, degree, q):
    # Tiny combinatorial models, including degree 2, test the general
    # port-counting lemma; they do not weaken the theorem's d>=3 scope.
    final_holes = set(range(q))
    fixed_missing = {v*degree+degree-1 for v in final_holes}
    all_ports = set(range(n*degree))
    completed = Counter()
    fixed_port_completion = Counter()
    full_vertices = list(range(q, n))
    for filled in combinations(full_vertices, 2*degree):
        for ports in product(range(degree), repeat=2*degree):
            new_missing = {v*degree+p for v, p in zip(filled, ports)}
            for old in matchings(all_ports-fixed_missing-new_missing):
                for added in matchings(new_missing):
                    final = tuple(sorted(old+added))
                    completed[final] += 1
                    if all(p == degree-1 for p in ports):
                        fixed_port_completion[final] += 1
    candidates = list(matchings(all_ports-fixed_missing))
    counts = {m: count_sets(m, degree, final_holes, degree) for m in candidates}
    assert all(completed[m] == counts[m] for m in candidates)
    assert len(set(counts.values())) > 1  # completion is not uniform
    wrong_uniform = any(F(completed[m], sum(completed.values())) != F(1,len(candidates))
                        for m in candidates)
    wrong_fixed_ports = any(F(fixed_port_completion[m],sum(fixed_port_completion.values()))
                            != F(counts[m],sum(counts.values())) for m in candidates)
    assert wrong_uniform and wrong_fixed_ports
    return {'n':n, 'degree':degree, 'q':q, 'matching_count':len(candidates),
            'inverse_histories':sum(completed.values()),
            'exact_M_density':True, 'uniform_completion_negative_control':wrong_uniform,
            'fixed_missing_port_negative_control':wrong_fixed_ports}


def force_legal(ports, x, legal):
    candidates = list(matchings(ports)); out = Counter()
    for m in candidates:
        mate = {a:b for a,b in m} | {b:a for a,b in m}
        z = mate[x]
        if z in legal:
            out[m] += F(1,len(candidates))
        else:
            for y in legal:
                w = mate[y]
                edges = set(m)
                edges.remove(tuple(sorted((x,z))))
                edges.remove(tuple(sorted((y,w))))
                edges.add(tuple(sorted((x,y))))
                edges.add(tuple(sorted((z,w))))
                out[tuple(sorted(edges))] += F(1,len(candidates)*len(legal))
    good = [m for m in candidates if any(x in e and bool(set(e)&legal) for e in m)]
    assert set(out)==set(good)
    assert all(v==F(1,len(good)) for v in out.values())
    return {'ports':len(ports), 'legal_partners':len(legal),
            'unconditional_matchings':len(candidates), 'conditional_matchings':len(good),
            'exact_switch_law':True}


def scales():
    a,b,rho = F(9,10),F(3,4),F(1,8)
    exponents = {'q_over_n':a-1, 's_over_q':b-a,
                 'tilt_covariance':(a-1)/2,
                 'convex_score':F(1,2)+rho-b,
                 'rho':-rho, 'score_count':-b/2,
                 's_increment':b-1}
    assert all(e<0 for e in exponents.values())
    assert not (F(1,2)+rho-F(1,2)<0)
    assert not (b-b<0)
    return {'exponents':{k:str(v) for k,v in exponents.items()},
            'sqrt_n_intensity_negative_control':True,
            's_equal_q_negative_control':True}


def main():
    result={'status':'PASS_FINITE_DIAGNOSTICS_ONLY',
            'bond':[bond(4,2,0),bond(6,2,2)],
            'switch':[force_legal(range(8),0,{1,2,3}),force_legal(range(10),0,{2,4,6,8})],
            'scales':scales()}
    print(json.dumps(result,sort_keys=True,indent=2))


if __name__=='__main__':
    main()
