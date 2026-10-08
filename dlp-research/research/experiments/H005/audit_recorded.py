"""Audit retained H005 JSON only; no import or execution of either solver."""
import hashlib
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path

base = Path('research/experiments/H005')
files = {
    'inverse_initial_results.json': '151564f18a315d81d6a88ade8daca0ce2804438691ffb6a02113bada5ec2e616',
    'inverse_walk.py': '968c1886389556eda86478f3c2f26a6741b2b908053dde5e182456f3173f1731',
    'inverse_walk_protocol.md': 'ee3425fd9f15021f1e6e76031f5da525ec091ba8d29bcd77a5f3a6978ff71f75',
}
for name, expected in files.items():
    assert hashlib.sha256((base / name).read_bytes()).hexdigest() == expected
D = json.loads((base / 'inverse_initial_results.json').read_text())
assert D['source_sha256'] == files['inverse_walk.py']
assert D['protocol_sha256'] == files['inverse_walk_protocol.md']
assert D['status'] == 'complete' and 'error' not in D
assert D['active_phase'] == {'phase': 'complete'}
assert D['partial_phase_event_vector'] == {}
assert D['verified_improvement'] == 'NONE'
assert D['fixture'] == {'G': [34, 35], 'Q': [4, 47], 'a': 28, 'b': 27, 'p': 59, 'q': 73}
assert D['bounds'] == {'T': 18, 'baby_m': 6, 'events': 1000000, 'giant_max': 6, 'seconds': 60.0}
records = D['completed_attempts']
assert [r['restart'] for r in records] == list(range(73))
summed = Counter()
outcomes = Counter()
cycles = Counter()
transitions = 0
for r in records:
    t = r['transitions']
    assert isinstance(t, int) and 0 <= t <= 18
    assert r['peak_dictionary_records'] == t
    v = r['events']
    assert all(isinstance(n, int) and n >= 0 for n in v.values())
    assert v.get('score_evaluations', 0) == 2*t
    assert v.get('table_writes', 0) == t
    assert v.get('scalar_multiplications', 0) == 1+t+int(r['verified'])
    assert v.get('answer_verifications', 0) == int(r['verified'])
    assert v.get('integer_inversions', 0) == int(r['verified'])
    if r['verified']:
        assert r['recovered_scalar'] == 70
        assert r['outcome'] in ('useful_cycle', 'identity_hit', 'minus_generator_hit')
        if r['outcome'] == 'useful_cycle':
            assert r['cycle_length'] in (5, 7) and r['cycle_length'] <= t
            cycles[r['cycle_length']] += 1
        else:
            assert r['cycle_length'] is None
    else:
        assert r['outcome'] == 'timeout' and t == 18
        assert r['recovered_scalar'] is None and r['cycle_length'] is None
    # This checks only integer call-count metadata, not scalar multiplication.
    restart = r['restart']
    scalar_calls = 0 if restart == 0 else restart.bit_count()+restart.bit_length()-1
    assert v['group_additions'] == scalar_calls+1+9*t+9*int(r['verified'])
    summed.update(v)
    outcomes[r['outcome']] += 1
    transitions += t
S = sum(r['verified'] for r in records)
assert S == 62 and outcomes['timeout'] == 11
assert outcomes['identity_hit'] == 2 and outcomes['minus_generator_hit'] == 1
assert outcomes['useful_cycle'] == 59
assert transitions == 745
assert max(r['peak_dictionary_records'] for r in records) == 18
phases = D['phase_event_vectors']
assert set(phases) == {'admission', 'candidate_setup', 'diagnostic_restart_enumeration', 'diagnostic_expectation_metadata', 'signed_bsgs'}
assert phases['diagnostic_restart_enumeration'] == {'loop_iterations': 73}
total = summed.copy()
for v in phases.values():
    total.update(v)
assert total == Counter(D['total_event_vector'])
assert sum(total.values()) == D['total_instrumented_events'] == 822726
assert D['reconciliation'] == {'equals_global_total': True, 'equals_global_vector': True, 'sum_partition_events': 822726}
assert 0 <= D['elapsed_seconds_through_computation'] <= 60
E = D['candidate_expected_work']
assert E['attempts'] == 73 and E['successes'] == 62 and E['success_probability'] == [62, 73]
assert E['sum_all_attempt_event_vectors'] == dict(summed)
setup = phases['candidate_setup']
sampler = {'comparisons': 128, 'loop_iterations': 1024, 'unbiased_bits': 896, 'integer_left_shifts': 896, 'integer_ors': 896}
categories = set(setup) | set(summed) | set(sampler)
assert set(E['expected_solver_events']) == categories
assert set(E['expected_attempt_events_including_sampler']) == categories
for c in categories:
    num = summed.get(c, 0)+sampler.get(c, 0)
    assert E['expected_attempt_events_including_sampler'][c] == [num, 73]
    assert E['expected_solver_events'][c] == [setup.get(c, 0)*62+num, 62]
sm = E['sampler']
assert sm['unbiased_bits_per_raw_draw'] == 7 and sm['runtime_draws_executed'] == 0
for label, value in [('raw_draws', 128), ('bits', 896)]:
    assert sm['expected_'+label+'_per_attempt'] == [value, 73]
    assert sm['expected_'+label+'_per_solve'] == [value, 62]
assert sm['expected_event_vector_per_attempt'] == {c: [n, 73] for c, n in sampler.items()}
assert sm['expected_event_vector_per_solve'] == {c: [n, 62] for c, n in sampler.items()}
assert D['total_event_vector'].get('unbiased_bits', 0) == 0
assert D['total_event_vector'].get('integer_ors', 0) == 0
ref = D['reference']
assert ref == {'baby_records': 7, 'giant_index': 0, 'peak_dictionary_records': 7, 'recovered_scalar': 70, 'verified': True}
assert phases['signed_bsgs']['group_additions'] == 17
assert phases['signed_bsgs']['field_inversions'] == 15
raw = {c: Fraction(*v) for c, v in E['expected_solver_events'].items()}
assert raw['group_additions'] == Fraction(4179, 31)
assert raw['field_inversions'] == Fraction(3707, 31)
corrected = raw.copy()
for c in ('loop_iterations', 'comparisons'):
    corrected[c] += Fraction(73, 62)
assert corrected['loop_iterations'] == Fraction(58609, 62)
assert corrected['comparisons'] == Fraction(236741, 62)
assert raw['group_additions']-9 == Fraction(3900, 31)
print('PASS hashes, 73 records, all recoveries=70, exact partitions and expectations')
print('outcomes', dict(outcomes), 'useful_cycle_lengths', dict(cycles), 'transitions', transitions)
print('actual_events', sum(total.values()), 'success_probability', Fraction(S, 73))
print('group_calls', raw['group_additions'], 'reference', phases['signed_bsgs']['group_additions'])
print('field_inversions', raw['field_inversions'], 'reference', phases['signed_bsgs']['field_inversions'])
print('wrapper_corrected_loops', corrected['loop_iterations'], 'comparisons', corrected['comparisons'])
