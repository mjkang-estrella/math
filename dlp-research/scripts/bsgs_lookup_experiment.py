"""Bounded synthetic BSGS cost experiment, not a timing or tape-cost claim.

Build the baby table afresh for every target. Count group-add API calls,
point comparisons in lookup, and key comparisons in merge-sort separately.
Coordinates use Python integers; internal arithmetic, allocation, indexing,
serialization, negation, and peak memory are NOT priced by these counters.
The table holds ceil(sqrt(q)) entries, plus merge-sort temporaries.
"""
from dataclasses import dataclass, asdict
from math import isqrt
import json


@dataclass
class Cost:
    adds: int = 0
    lookup_comparisons: int = 0
    sort_comparisons: int = 0


@dataclass(frozen=True)
class Curve:
    p: int
    a: int
    b: int
    generator: tuple
    q: int

    def add(self, left, right, cost=None):
        if cost is not None:
            cost.adds += 1
        if left is None:
            return right
        if right is None:
            return left
        x, y = left
        u, v = right
        if x == u and (y + v) % self.p == 0:
            return None
        numerator, denominator = ((3*x*x + self.a, 2*y) if left == right
                                  else (v-y, u-x))
        slope = numerator * pow(denominator % self.p, -1, self.p) % self.p
        xx = (slope*slope - x - u) % self.p
        return xx, (slope*(x-xx) - y) % self.p

    def neg(self, point):
        return None if point is None else (point[0], -point[1] % self.p)


def key(point):
    return (0, 0, 0) if point is None else (1, *point)


def merge_sort(entries, cost):
    if len(entries) <= 1:
        return entries
    mid = len(entries)//2
    left = merge_sort(entries[:mid], cost)
    right = merge_sort(entries[mid:], cost)
    i = j = 0
    out = []
    while i < len(left) and j < len(right):
        cost.sort_comparisons += 1
        if key(left[i][0]) <= key(right[j][0]):
            out.append(left[i]); i += 1
        else:
            out.append(right[j]); j += 1
    return out + left[i:] + right[j:]


def lookup(entries, target, ordered, cost):
    if not ordered:
        for point, scalar in entries:
            cost.lookup_comparisons += 1
            if point == target:
                return scalar
        return None
    lo, hi = 0, len(entries)
    target_key = key(target)
    while lo < hi:
        mid = (lo + hi)//2
        point, scalar = entries[mid]
        # One equality and, on failure, one ordering comparison are charged.
        cost.lookup_comparisons += 1
        if key(point) == target_key:
            return scalar
        cost.lookup_comparisons += 1
        if key(point) < target_key:
            lo = mid + 1
        else:
            hi = mid
    return None


def bsgs(curve, target, ordered):
    m = isqrt(curve.q - 1) + 1
    cost = Cost()
    babies = []
    current = None
    for j in range(m):
        babies.append((current, j))
        current = curve.add(current, curve.generator, cost)
    stride = curve.neg(current)  # current = mG; negation excluded explicitly
    if ordered:
        babies = merge_sort(babies, cost)
    current = target
    blocks = (curve.q + m - 1)//m
    for i in range(blocks):
        j = lookup(babies, current, ordered, cost)
        if j is not None:
            candidate = i*m + j
            if candidate < curve.q:
                return candidate, cost
        if i + 1 < blocks:
            current = curve.add(current, stride, cost)
    return None, cost


def exhaustive(curve, target):
    cost = Cost()
    current = None
    for d in range(curve.q):
        cost.lookup_comparisons += 1
        if current == target:
            return d, cost
        current = curve.add(current, curve.generator, cost)
    return None, cost


def main():
    curves = [Curve(5, 2, 1, (0, 1), 7), Curve(17, 2, 2, (0, 6), 19),
              Curve(43, 0, 7, (2, 12), 31), Curve(101, 1, 46, (2, 37), 109),
              Curve(211, 0, 2, (4, 53), 199)]
    rows = []
    counted_events = 0
    for curve in curves:
        assert all(curve.p % d for d in range(2, isqrt(curve.p)+1))
        assert (4*curve.a**3 + 27*curve.b**2) % curve.p != 0
        points = {None} | {(x, y) for x in range(curve.p) for y in range(curve.p)
                           if (y*y-x**3-curve.a*x-curve.b) % curve.p == 0}
        assert len(points) == curve.q
        orbit = []
        current = None
        for _ in range(curve.q):
            assert current in points and current not in orbit
            orbit.append(current)
            current = curve.add(current, curve.generator)
        assert current is None and set(orbit) == points
        m = isqrt(curve.q-1)+1
        costs = {name: [] for name in ('exhaustive', 'linear_bsgs', 'ordered_bsgs')}
        for secret, target in enumerate(orbit):
            for name in costs:
                result, cost = (exhaustive(curve, target) if name == 'exhaustive'
                                else bsgs(curve, target, name == 'ordered_bsgs'))
                assert result == secret
                if name != 'ordered_bsgs':
                    assert cost.lookup_comparisons == secret+1
                if name != 'exhaustive':
                    assert cost.adds == m + secret//m
                costs[name].append(cost)
                counted_events += sum(asdict(cost).values())
                assert counted_events < 1_000_000
        row = {'curve': asdict(curve), 'secrets_tested': len(orbit), 'baby_entries': m}
        for name, samples in costs.items():
            row[name] = {field: max(getattr(c, field) for c in samples)
                         for field in Cost.__dataclass_fields__}
            row[name]['max_sort_plus_lookup'] = max(
                c.sort_comparisons+c.lookup_comparisons for c in samples)
        rows.append(row)
    print(json.dumps({'rows': rows, 'counted_algorithm_events': counted_events,
                      'units': 'API additions and point/key comparisons; no timing or tape claims',
                      'scope': 'all scalars on five fixed synthetic curves; no frozen hard family'},
                     indent=2))


if __name__ == '__main__':
    main()
