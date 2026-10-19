#!/usr/bin/env python3
"""Exact finite interface controls; no source counter and no proof certificate.

The two tree computations are deliberately different: global estimate assignment
and leaf summation versus lazy recursive scalar-history enumeration.
"""
from fractions import Fraction as F
from itertools import product
from math import comb
import json


def cdf_median(law, repetitions, wrong_threshold=False):
    cumulative = previous = F(0)
    result = {}
    threshold = repetitions // 2 + (0 if wrong_threshold else 1)
    for value, weight in sorted(law.items()):
        cumulative += weight
        current = sum((F(comb(repetitions, j)) * cumulative**j *
                       (1-cumulative)**(repetitions-j)
                       for j in range(threshold, repetitions+1)), F(0))
        result[value] = current-previous
        previous = current
    return result


def literal_median(tapes, repetitions):
    result = dict.fromkeys(tapes, F(0))
    for draws in product(tapes, repeat=repetitions):
        value = sorted(draws)[repetitions//2]
        result[value] += F(1, len(tapes)**repetitions)
    return result


def instance(codes, depth, repetitions):
    prefixes = sorted({code[:i] for code in codes for i in range(depth+1)})
    counts = {p: sum(code.startswith(p) for code in codes) for p in prefixes}
    laws = {}
    for prefix in prefixes:
        if len(prefix) == depth:
            laws[prefix] = {F(1): F(1)}
            continue
        base = {}
        for value, weight in [(F(counts[prefix]), F(3, 4)),
                              (F(0), F(1, 8)), (F(2**(depth+1)), F(1, 8))]:
            clipped = max(F(1), min(F(2**depth), value))
            base[clipped] = base.get(clipped, F(0))+weight
        laws[prefix] = cdf_median(base, repetitions)
    return prefixes, counts, laws


def global_assignments(codes, depth, repetitions):
    prefixes, counts, laws = instance(codes, depth, repetitions)
    variables = [p for p in prefixes if len(p) < depth]
    accepted = dict.fromkeys(codes, F(0))
    good_mass = dict.fromkeys(codes, F(0))
    bad_mass = dict.fromkeys(codes, F(0))
    assignments = 0
    for choices in product(*(list(laws[p].items()) for p in variables)):
        assignment_weight = F(1)
        values = {p: F(1) for p in prefixes if len(p) == depth}
        for p, (value, weight) in zip(variables, choices):
            values[p] = value
            assignment_weight *= weight
        good = all(values[p] == counts[p] for p in variables)
        assignments += 1
        for leaf in codes:
            proposal = F(1)
            for i in range(depth):
                p = leaf[:i]
                children = [p+b for b in '01' if p+b in laws]
                if len(children) == 2:
                    proposal *= values[leaf[:i+1]]/sum(values[c] for c in children)
            mass = assignment_weight * proposal * min(F(1), 1/(4*values['']*proposal))
            accepted[leaf] += mass
            (good_mass if good else bad_mass)[leaf] += mass
    assert len(set(good_mass.values())) == 1
    assert all(accepted[x] == good_mass[x]+bad_mass[x] for x in codes)
    return accepted, good_mass, bad_mass, assignments


def lazy_histories(codes, depth, repetitions, omit_q=False):
    _, _, laws = instance(codes, depth, repetitions)
    accepted = dict.fromkeys(codes, F(0))
    histories = 0

    def descend(p, mass, proposal, root):
        nonlocal histories
        if len(p) == depth:
            denom = 4*root*(1 if omit_q else proposal)
            accepted[p] += mass * min(F(1), 1/denom)
            histories += 1
            return
        children = [p+b for b in '01' if p+b in laws]
        if len(children) == 1:
            descend(children[0], mass, proposal, root)
        else:
            left, right = children
            for a, wa in laws[left].items():
                for b, wb in laws[right].items():
                    for child, probability in [(left, a/(a+b)), (right, b/(a+b))]:
                        descend(child, mass*wa*wb*probability,
                                proposal*probability, root)
    for root, weight in laws[''].items():
        descend('', weight, F(1), root)
    return accepted, histories


def normalized(masses):
    return {x: p/sum(masses.values()) for x, p in masses.items()}


def run():
    median_cases = 0
    threshold_detected = False
    for tapes in [(F(1), F(1), F(2), F(7)), (F(1, 3), F(2), F(5), F(5)),
                  (F(2),)*4, (F(1), F(1), F(1), F(9))]:
        law = {x: F(tapes.count(x), len(tapes)) for x in set(tapes)}
        for repetitions in [1, 3, 5]:
            literal = literal_median(tapes, repetitions)
            assert cdf_median(law, repetitions) == literal
            threshold_detected |= cdf_median(law, repetitions, True) != literal
            median_cases += 1
    fixtures = [(1, ('0',)), (1, ('0', '1')),
                (2, ('00', '01', '11')), (3, ('000', '001', '010', '111')),
                (3, ('001', '101'))]
    tree_cases = assignments = histories = 0
    bad_mass_changes_law = omit_q_detected = non_dyadic_seen = False
    restart_normalization_detected = False
    history_counts = {}
    largest_denominator_bits = 0
    for depth, codes in fixtures:
        fixture_counts = []
        for repetitions in [1, 3, 5, 9]:
            full, good, bad, count = global_assignments(codes, depth, repetitions)
            lazy, h = lazy_histories(codes, depth, repetitions)
            assert full == lazy
            law = normalized(full)
            assert sum(law.values()) == 1
            assert 0 < sum(full.values()) <= 1
            assert all(p >= 0 for p in law.values())
            uniform = F(1, len(codes))
            bad_mass_changes_law |= law != normalized(good)
            omit_q_detected |= normalized(lazy_histories(codes, depth, repetitions, True)[0]) != law
            restart_normalization_detected |= full != law
            for p in law.values():
                denom = p.denominator
                non_dyadic_seen |= bool(denom & (denom-1))
                largest_denominator_bits = max(largest_denominator_bits, denom.bit_length())
            retained = min(uniform/p for p in law.values())/2
            delta = 1-retained
            residual = {x: (uniform-retained*law[x])/delta for x in codes}
            assert all(p >= 0 for p in residual.values())
            assert sum(residual.values()) == 1
            assert all(retained*law[x]+delta*residual[x] == uniform for x in codes)
            # Forgetting division by success does not give a probability law.
            unnormalized_residual = {x: (uniform-retained*full[x])/delta for x in codes}
            if sum(full.values()) < 1:
                assert sum(unnormalized_residual.values()) != 1
            fixture_counts.append(h)
            tree_cases += 1
            assignments += count
            histories += h
        assert len(set(fixture_counts)) == 1
        history_counts['/'.join(codes)] = fixture_counts[0]
    assert all([threshold_detected, bad_mass_changes_law, omit_q_detected,
                restart_normalization_detected, non_dyadic_seen])
    # Exact finite rational-coin loop integration, including a non-dyadic coin.
    coin_cases = 0
    for denominator in range(1, 25):
        bits = (denominator-1).bit_length()
        for numerator in range(denominator+1):
            one_attempt_mass = F(numerator, 2**bits)
            one_attempt_success = F(denominator, 2**bits)
            assert one_attempt_mass/one_attempt_success == F(numerator, denominator)
            coin_cases += 1
    return dict(status='FINITE_INTERFACE_CONTROLS_PASSED', median_cases=median_cases,
                tree_cases=tree_cases, full_assignments=assignments, macro_histories=histories,
                history_counts_independent_of_repetitions=history_counts,
                rational_coin_cases=coin_cases,
                largest_observed_denominator_bits=largest_denominator_bits,
                mutations_detected=dict(wrong_median_threshold=threshold_detected,
                    drop_bad_estimates=bad_mass_changes_law, omit_Q=omit_q_detected,
                    skip_restart_normalization=restart_normalization_detected),
                non_dyadic_actual_law_observed=non_dyadic_seen,
                limit='Mock bounded counter only; no source FPRAS implementation, asymptotic proof, correctness PASS, or contribution certificate.')


if __name__ == '__main__':
    print(json.dumps(run(), indent=2, sort_keys=True))
