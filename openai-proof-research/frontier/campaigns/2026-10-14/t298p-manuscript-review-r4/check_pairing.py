#!/usr/bin/env python3
"""Exact finite pairing diagnostic; no analytic/entropy theorem is tested."""
import itertools
import json
from functools import lru_cache


@lru_cache(None)
def tau(w):
    if not w:
        return 1
    if len(w) % 2:
        return 0
    return sum(tau(w[1:j]) * tau(w[j+1:])
               for j in range(1, len(w)) if w[j] == w[0])


def ds(w):
    return [(w[:i], w[i+1:]) for i, x in enumerate(w) if x == 's']


def inserted_trace(u, v, p):
    return sum(tau(l+u) * tau(v+r) for l, r in ds(p))


def printed_score_pair(u, v, p):
    return (tau(u+'s'+v+p)
            - sum(tau(r)*tau(l+v+p) for l, r in ds(u))
            - sum(tau(l)*tau(u+r+p) for l, r in ds(v)))


def corrected_score_pair(u, v, p):
    return (tau(v+'s'+u+p)
            - sum(tau(l)*tau(v+r+p) for l, r in ds(u))
            - sum(tau(r)*tau(l+u+p) for l, r in ds(v)))


def words(max_length):
    return [''.join(w) for n in range(max_length+1)
            for w in itertools.product('st', repeat=n)]


def main():
    # s and t are centered free standard semicirculars. xi_s=s relative to t.
    # The printed equation is a valid conventional Hilbert-adjoint formula;
    # this tests its unconverted use under the paper's bilinear score pairing.
    u, v, p = 't', '', 'ts'
    witness = {'u': u, 'v': '1', 'P': p,
               'inserted_derivative_trace': inserted_trace(u, v, p),
               'printed_rhs_paired_bilinearly': printed_score_pair(u, v, p),
               'corrected_score_paired_bilinearly': corrected_score_pair(u, v, p)}
    assert witness['inserted_derivative_trace'] == 1
    assert witness['printed_rhs_paired_bilinearly'] == 0
    assert witness['corrected_score_paired_bilinearly'] == 1
    count = 0
    mismatches = 0
    for u, v, p in itertools.product(words(2), words(2), words(4)):
        actual = inserted_trace(u, v, p)
        assert actual == corrected_score_pair(u, v, p), (u, v, p)
        mismatches += actual != printed_score_pair(u, v, p)
        count += 1
    assert mismatches > 0
    print(json.dumps({'scope': 'exact finite pairing/convention diagnostic only',
                      'witness': witness, 'corrected_identity_cases': count,
                      'unconverted_printed_formula_mismatches': mismatches}, indent=2))


if __name__ == '__main__':
    main()
