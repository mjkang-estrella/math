"""Independent low-position cover, retaining distinctness of fixed positions.

No generator, checker or legacy coverage imports. A state contains a constant,
remaining labelled coefficients, individual floors and the already fixed q's.
When splitting one coordinate at a certificate floor, its low values already in
the fixed set are impossible in the ORIGINAL domain and may be discarded.
No restriction is imposed on free/free or free/fixed collisions in a terminal
certificate: those enlarged domains still safely contain every original point.
"""
import collections


def distinct_cover(K, coefficients, available):
    todo = [(K, tuple(coefficients), (3,) * len(coefficients), ())]
    seen = set()
    used = set()
    skipped = 0
    bound = 2
    while todo:
        constant, cs, floors, fixed = todo.pop()
        state = (constant, cs, floors, fixed)
        if state in seen:
            continue
        seen.add(state)
        options = available.get((constant, tuple(sorted(cs))), [])
        floor = min(q for q, path in options) if options else max(3, (constant & -constant).bit_length())
        bound = max(bound, floor - 1)
        offending = next((i for i, q in enumerate(floors) if q < floor), None)
        if offending is None:
            assert options, ('missing distinct-fixed domain', constant, cs, floors, fixed)
            used.add(next(path for q, path in options if q == floor))
            continue
        i = offending
        high = list(floors)
        high[i] = floor
        todo.append((constant, cs, tuple(high), fixed))
        for q in range(floors[i], floor):
            if q in fixed:
                skipped += 1
                continue
            todo.append((constant + cs[i] * 10**q, cs[:i] + cs[i + 1:],
                         floors[:i] + floors[i + 1:], tuple(sorted(fixed + (q,)))))
        assert len(seen) < 3000000, 'distinct coverage state cap'
    return {'domain_count': len(used), 'domains': sorted(used), 'finite_Lmax': bound,
            'states': len(seen), 'impossible_fixed_collision_branches': skipped,
            'coverage_method': 'distinct_fixed_positions'}


def position_cover(K, coefficients, available, extra_floor=2):
    """A second cover: decide each position once, including the digit-1 choice."""
    todo = [(K, tuple(sorted(coefficients)), 3)]
    seen, used = set(), set()
    bound = 2
    while todo:
        a, cs, p = todo.pop()
        if (a, cs, p) in seen:
            continue
        seen.add((a, cs, p))
        options = available.get((a, cs), [])
        if options:
            q = min(v for v, path in options)
            bound = max(bound, q - 1)
            if p >= q:
                used.add(next(path for v, path in options if v == q))
                continue
        else:
            # This stopping threshold affects only failure/search time, not
            # acceptance: no branch can be accepted without a checked domain.
            floor = max(3, (a & -a).bit_length() + extra_floor)
            assert p < floor, ('missing position-partition domain', a, cs, p)
        todo.append((a, cs, p + 1))
        for coefficient, multiplicity in collections.Counter(cs).items():
            index = cs.index(coefficient)
            todo.append((a + coefficient * 10**p, cs[:index] + cs[index + 1:], p + 1))
        assert len(seen) < 3000000, 'position coverage state cap'
    return {'domain_count': len(used), 'domains': sorted(used), 'finite_Lmax': bound,
            'states': len(seen), 'coverage_method': 'position_partition'}


def finite_partition_test():
    """Test the splitting invariant on every labelled distinct tuple in small boxes.

    Certificate floors are deliberately synthetic and constant-dependent. The
    independent second enumeration forms the original tuples directly, without
    following the splitting decisions.
    """
    import itertools
    cases = points = discarded = 0
    for coefficients in ((9, 9), (9, 18), (9, 9, 18), (18, 27, 54)):
        for constant0 in (8, 98, 1223):
            for L in range(3, 9):
                terminal = set()
                seen = set()
                # Track original slot indices to reconstruct and compare tuples.
                todo = [(constant0, tuple(enumerate(coefficients)), (3,) * len(coefficients), ())]
                while todo:
                    constant, slots, floors, fixed = todo.pop()
                    if (constant, slots, floors, fixed) in seen:
                        continue
                    seen.add((constant, slots, floors, fixed))
                    floor = 3 + constant.bit_count() % 3
                    i = next((i for i, q in enumerate(floors) if q < floor), None)
                    if i is None:
                        options = [range(q, L) for q in floors]
                        for qs in itertools.product(*options):
                            allq = dict(fixed)
                            allq.update((slot, q) for (slot, c), q in zip(slots, qs))
                            pt = tuple(allq[j] for j in range(len(coefficients)))
                            if len(set(pt)) != len(pt) or any(q >= L for q in pt):
                                continue
                            assert constant + sum(c * 10**q for (slot, c), q in zip(slots, qs)) == constant0 + sum(c * 10**q for c, q in zip(coefficients, pt))
                            assert pt not in terminal
                            terminal.add(pt)
                        continue
                    high = list(floors)
                    high[i] = floor
                    todo.append((constant, slots, tuple(high), fixed))
                    for q in range(floors[i], floor):
                        if q in {value for slot, value in fixed}:
                            discarded += 1
                            continue
                        slot, c = slots[i]
                        todo.append((constant + c * 10**q, slots[:i] + slots[i + 1:],
                                     floors[:i] + floors[i + 1:], tuple(sorted(fixed + ((slot, q),)))))
                expected = set(itertools.permutations(range(3, L), len(coefficients)))
                assert terminal == expected
                cases += 1
                points += len(expected)
    return {'result': 'PASS', 'cases': cases, 'labelled_points': points,
            'discarded_fixed_collision_branches': discarded}


def finite_position_test():
    import itertools
    cases = points = 0
    for coefficients in ((9, 9), (9, 18), (9, 9, 18), (18, 27, 54)):
        def canonical(qs):
            return tuple(q for c in sorted(set(coefficients))
                         for q in sorted(q for d, q in zip(coefficients, qs) if c == d))
        for K in (8, 98, 1223):
            for L in range(3, 9):
                actual = set()
                todo = [(K, tuple(coefficients), 3, ())]
                while todo:
                    constant, cs, p, fixed = todo.pop()
                    if p >= 3 + constant.bit_count() % 3:
                        local = set()
                        for free in itertools.permutations(range(p, L), len(cs)):
                            assignments = fixed + tuple(zip(cs, free))
                            if any(q >= L for c, q in assignments):
                                continue
                            pt = tuple(q for c in sorted(set(coefficients))
                                       for q in sorted(q for d, q in assignments if d == c))
                            assert constant + sum(c * 10**q for c, q in zip(cs, free)) == K + sum(c * 10**q for c, q in zip(sorted(coefficients), pt))
                            local.add(pt)
                        assert not actual.intersection(local)
                        actual.update(local)
                        continue
                    todo.append((constant, cs, p + 1, fixed))
                    for c in set(cs):
                        rest = list(cs)
                        rest.remove(c)
                        todo.append((constant + c * 10**p, tuple(rest), p + 1, fixed + ((c, p),)))
                expected = {canonical(qs) for qs in itertools.permutations(range(3, L), len(coefficients))}
                assert actual == expected
                cases += 1
                points += len(expected)
    return {'result': 'PASS', 'cases': cases, 'canonical_points': points}


if __name__ == '__main__':
    import json
    import pathlib
    import sys
    sys.dont_write_bytecode = True
    result = finite_partition_test()
    result['position_partition'] = finite_position_test()
    (pathlib.Path(__file__).resolve().parent / 'distinct_cover_tests.json').write_text(json.dumps(result, indent=1) + '\n')
    print(json.dumps(result))
