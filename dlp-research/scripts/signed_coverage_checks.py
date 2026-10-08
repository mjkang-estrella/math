"""Finite independent cyclic-block checks; no group, timing or speed claim.

Enumerates *all* residues for q=1..64 and m=1..32, including m>q.
Each explicit signed-residue insertion counts one event; a one-million-event
limit bounds the run. Coverage is built without the proposed first-hit formula.
The formula and old/tight caps are checked against those enumerated first hits.
"""
import json


def main():
    profiles = 0
    scalar_cases = 0
    insertions = 0
    old_equal = 0
    old_extra = 0
    minimal_caps = 0
    for q in range(1, 65):
        for m in range(1, 33):
            radius = m - 1
            stride = 2 * m - 1
            tight = (q - 1) // stride + 1
            old = (q - 1 + radius) // stride + 1
            assert old in (tight, tight + 1), (q, m, old, tight)
            old_equal += old == tight
            old_extra += old == tight + 1
            first = [None] * q
            for i in range(tight):
                for j in range(m):
                    for residue in ((i * stride + j) % q,
                                    (i * stride - j) % q):
                        insertions += 1
                        assert insertions < 1_000_000
                        if first[residue] is None:
                            first[residue] = i
            assert all(x is not None for x in first), (q, m, first)
            for d, observed in enumerate(first):
                predicted = (0 if d <= radius or q <= d + radius
                             else (d + radius) // stride)
                assert observed == predicted, (q, m, d, observed, predicted)
                assert observed < tight <= old
                scalar_cases += 1
            # Some residue still needs the final center: this cap is minimal
            # for this sequential-center construction, not for all algorithms.
            assert max(first) == tight - 1, (q, m, first)
            minimal_caps += 1
            profiles += 1
    print(json.dumps({
        'scope': 'finite modular arithmetic; not an EC implementation or speed claim',
        'q_range_inclusive': [1, 64], 'm_range_inclusive': [1, 32],
        'profiles': profiles, 'scalar_cases': scalar_cases,
        'signed_residue_insertions': insertions,
        'old_cap_equals_tight': old_equal,
        'old_cap_one_extra': old_extra,
        'minimal_sequential_caps_checked': minimal_caps,
        'finding': 'all first hits precede tight cap; reducing the unused safe cap does not change early-stopping work'
    }, indent=2))


if __name__ == '__main__':
    main()
