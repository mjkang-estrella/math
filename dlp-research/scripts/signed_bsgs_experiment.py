"""Provisional known negation-map BSGS experiment; review required.

Shared sorted-table engine compares ordinary and signed blocks. Counter units
remain high-level API events, never tape steps or elapsed-time estimates.
Includes table construction, sorting, stride negation and canonicalization.
No field-operation, allocation, index-access or peak-byte bound is claimed.
"""
from dataclasses import dataclass, asdict
from math import isqrt
import json

from bsgs_lookup_experiment import Curve, Cost, merge_sort, lookup


@dataclass
class SignedCost(Cost):
    negations: int = 0
    canonical_order_tests: int = 0


def neg(curve, point, cost):
    cost.negations += 1
    return curve.neg(point)


def canonical(curve, point, cost):
    if point is None:
        return None, 1
    negative = neg(curve, point, cost)
    cost.canonical_order_tests += 1
    return (point, 1) if point[1] <= negative[1] else (negative, -1)


def solve(curve, target, m, signed):
    if not (1 <= m <= curve.q):
        raise ValueError('m outside full-domain table bounds')
    if signed and not 2*(m-1) < curve.q:
        raise ValueError('signed baby representatives may alias')
    cost = SignedCost()
    entries = []
    current = None
    last = None
    for j in range(m):
        if signed:
            representative, sign = canonical(curve, current, cost)
            entries.append((representative, sign*j))
        else:
            entries.append((current, j))
        last = current
        current = curve.add(current, curve.generator, cost)
    # current=mG, last=(m-1)G. Count the extra addition forming (2m-1)G.
    stride_point = curve.add(current, last, cost) if signed else current
    stride = neg(curve, stride_point, cost)
    entries = merge_sort(entries, cost)
    step = 2*m-1 if signed else m
    blocks = ((curve.q+m-2)//step+1 if signed else (curve.q+m-1)//m)
    current = target
    for i in range(blocks):
        representative, sign = (canonical(curve, current, cost) if signed
                                else (current, 1))
        digit = lookup(entries, representative, True, cost)
        if digit is not None:
            candidate = i*step + sign*digit
            if signed:
                return candidate % curve.q, cost
            if candidate < curve.q:
                return candidate, cost
        if i+1 < blocks:
            current = curve.add(current, stride, cost)
    return None, cost


def main():
    curves = [Curve(5,2,1,(0,1),7), Curve(17,2,2,(0,6),19),
              Curve(43,0,7,(2,12),31), Curve(101,1,46,(2,37),109),
              Curve(211,0,2,(4,53),199)]
    total_events = 0
    rows = []
    for curve in curves:
        # Same fixed challenge set as W004, independently revalidated here.
        assert all(curve.p % d for d in range(2, isqrt(curve.p)+1))
        assert (4*curve.a**3 + 27*curve.b**2) % curve.p != 0
        points = {None} | {(x,y) for x in range(curve.p) for y in range(curve.p)
                           if (y*y-x**3-curve.a*x-curve.b) % curve.p == 0}
        orbit = []
        current = None
        for _ in range(curve.q):
            assert current in points and current not in orbit
            orbit.append(current)
            current = curve.add(current, curve.generator)
        assert current is None and set(orbit) == points
        m_plain = isqrt(curve.q-1)+1
        m_signed = isqrt((curve.q-1)//2)+1  # ceil(sqrt(q/2)) exactly
        configurations = [('ordinary', m_plain, False),
                          ('signed_same_m', m_plain, True),
                          ('signed_smaller_table', m_signed, True)]
        row = {'curve': asdict(curve), 'secrets_tested': len(orbit)}
        for name, m, signed in configurations:
            samples = []
            for secret, target in enumerate(orbit):
                result, cost = solve(curve, target, m, signed)
                assert result == secret, (name, curve, secret, result)
                samples.append(cost)
                total_events += sum(asdict(cost).values())
                assert total_events < 1_000_000
            row[name] = {'m': m,
                         'maxima': {k: max(getattr(c,k) for c in samples)
                                    for k in SignedCost.__dataclass_fields__},
                         'totals_all_secrets': {k: sum(getattr(c,k) for c in samples)
                                               for k in SignedCost.__dataclass_fields__}}
        rows.append(row)
    print(json.dumps({'rows': rows, 'counted_events': total_events,
                      'scope': 'provisional finite negation-map experiment; no time/tape claim',
                      'memory': 'm baby entries plus merge-sort temporaries; not peak bytes'},
                     indent=2))


if __name__ == '__main__':
    main()
