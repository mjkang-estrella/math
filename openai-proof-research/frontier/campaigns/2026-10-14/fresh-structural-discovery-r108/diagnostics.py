"""Exact finite controls only. Prints JSON; no writes, network, or subprocesses."""
from fractions import Fraction as F
import json


def positive_attractor(owner, edges, target, player):
    current = set(target)
    while True:
        nxt = set(current)
        for v in owner:
            support = [u for u, probability in edges[v] if probability > 0]
            assert support
            existential = owner[v] in (player, 'Chance')
            if (any(u in current for u in support) if existential
                    else all(u in current for u in support)):
                nxt.add(v)
        if nxt == current:
            return current
        current = nxt


def main():
    owner = {'s': 'Chance', 'g': 'Max', 'b': 'Max'}
    fractions = sorted({F(a, b) for b in range(2, 18) for a in range(1, b)})
    rows = []
    for probability in fractions:
        edges = {'s': [('g', probability), ('b', 1 - probability)],
                 'g': [('g', F(1))], 'b': [('b', F(1))]}
        # Exact absorption after one step. All later rewards are zero and the
        # recurring priority is 2 at g and 1 at b.
        success = {v: sum(q for u, q in edges[v] if u == 'g') for v in owner}
        actual_as = {v for v in owner if success[v] == 1}
        literal_transfer = positive_attractor(owner, edges, {'g'}, 'Max')
        assert actual_as == {'g'} and literal_transfer == {'s', 'g'}
        assert positive_attractor(owner, edges, {'s', 'b'}, 'Min') == {'s', 'b'}
        # Removing actual_as does NOT give a chance-closed restriction.
        assert any(u == 'g' and q > 0 for u, q in edges['s'])
        rows.append({'p': str(probability), 'success_s': str(success['s'])})
    endpoints = []
    for probability in (F(0), F(1)):
        edges = {'s': [('g', probability), ('b', 1-probability)],
                 'g': [('g', F(1))], 'b': [('b', F(1))]}
        observed = positive_attractor(owner, edges, {'g'}, 'Max')
        assert observed == ({'g'} if probability == 0 else {'s', 'g'})
        endpoints.append({'p': str(probability), 'positive_max': sorted(observed)})

    # An independently specified gain/bias fixture: the Min gain-increasing
    # edge has negative immediate reward, and chance residuals have both signs.
    gain = {'g': F(0), 'b': F(2), 's': F(1), 'm': F(0)}
    bias = dict.fromkeys(gain, F(0))
    edges = {'g': [('g', F(0), F(1))], 'b': [('b', F(2), F(1))],
             's': [('g', F(1), F(1,2)), ('b', F(1), F(1,2))],
             'm': [('g', F(0), F(1)), ('b', F(-7), F(1))]}
    W = max(abs(w) for outgoing in edges.values() for _, w, _ in outgoing)
    B = max(abs(b) for b in bias.values())
    delta = min(abs(a-b) for a in gain.values() for b in gain.values() if a != b)
    multiplier = (W+2*B)/delta
    potential = {v: bias[v]+multiplier*gain[v] for v in gain}
    residual = {v: [w+potential[u]-potential[v] for u,w,_ in edges[v]] for v in gain}
    assert all(r >= 0 for v in ('g','b','m') for r in residual[v])
    assert sum(q*gain[u] for u,_,q in edges['s']) == gain['s']
    assert sum(q*(w+bias[u]-bias['s']) for u,w,q in edges['s']) == gain['s']
    chance_mean = sum(q*r for (_,_,q),r in zip(edges['s'],residual['s']))
    assert chance_mean == gain['s'] and min(residual['s']) < 0
    assert max(residual['s']) > 0
    # This check guards against treating the stochastic prefix bound as
    # nonnegative on each possible edge.
    print(json.dumps({'status': 'finite_controls_only_not_a_general_proof',
                      'interior_rationals_checked': len(rows),
                      'rational_cases': rows, 'endpoint_controls': endpoints,
                      'potential_fixture': {'multiplier': str(multiplier),
                        'residuals': {v:list(map(str,rs)) for v,rs in residual.items()},
                        'chance_mean': str(chance_mean)},
                      'full_target': 'UNRESOLVED', 'count_change': 0},
                     indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
