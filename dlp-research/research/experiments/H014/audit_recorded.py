"""Independent Sol audit, retained by root; recorded JSON arithmetic only.

Run from dlp-research. Does not import the experiment or recompute field/group
operations. This verifies the saved evidence, not cryptographic correctness or
an ECDLP improvement. Constants identify the frozen first run.
"""
import json
import hashlib
from pathlib import Path
from collections import Counter

r = json.loads(Path('research/experiments/H014/initial_results.json').read_text())

def add(x, y): return (x[0]+y[0], x[1]+y[1])
def conj(x): return (x[0]+x[1], -x[1])
def mul(x, y): return (x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0]+x[1]*y[1])
def norm(x): return x[0]*x[0]+x[0]*x[1]+x[1]*x[1]

ph = Counter()
for v in r['phase_category_counts'].values(): ph.update(v)
assert dict(ph) == r['category_counts'] and sum(ph.values()) == 738704 == r['instrumented_events']
assert sum(r['storage_entries_by_table'].values()) == 8979 == r['algorithm_storage_entries'] == r['peak_algorithm_storage_entries']
assert r['status'] == 'COMPLETE' and r['completed_fields'] == 3 and r['admission_incomplete_fields'] == 0
assert sum(f['candidate_count'] for f in r['fields']) == 148 == r['category_counts']['curve_candidates']
for f in r['fields']:
    q, p = f['q'], f['p']; N = q-1; base = f['generators'][0]['measurement_rows']
    cache = {tuple(x['point']): [tuple(v) for v in (x['sign'], x['par'], x['even'])] for x in f['feature_rows']}
    chi = {x['n']: tuple(x['chi']) for x in base}
    plant = {tuple(x['point']): tuple(x['features'][3]) for x in base}
    assert len(cache) == len(base) == N and f['candidate_count'] == len(f['candidates'])
    assert f['candidates'][-1]['status'] == 'ADMITTED' and sum(c['status'] == 'ADMITTED' for c in f['candidates']) == 1
    energy = [sum(norm(v[j]) for v in cache.values()) for j in range(2)]; null = [2*v for v in energy]
    ref = f['ideal_signed_pair_null']
    assert ref['energy_sums'] == energy and ref['second_moment_numerators'] == null and ref['second_moment_denominator'] == N*N
    G = []
    for gi, g in enumerate(f['generators']):
        sums = [(0, 0)]*4; zeros = [0]*4
        assert g['orbit_complete'] and g['measurement_complete'] and g['exact_controls_verified']
        for n, x in enumerate(g['measurement_rows'], 1):
            vals = [tuple(v) for v in x['features']]
            assert x['complete'] and x['n'] == n and tuple(x['chi']) == chi[n]
            assert vals[:3] == cache[tuple(x['point'])] and vals[3] == plant[tuple(x['point'])]
            for j in range(4):
                sums[j] = add(sums[j], mul(vals[j], conj(chi[n])))
                zeros[j] += (vals[j] == (0, 0))
            assert [tuple(v) for v in x['accumulated_feature_prefix']] == sums
        for rec, s in zip(g['sums'], sums):
            assert tuple(rec['pair']) == s and rec['denominator'] == N and rec['squared_magnitude_denominator'] == N*N and rec['squared_magnitude_numerator'] == norm(s)
        assert g['zero_counts'] == zeros and sums[2] == (0, 0)
        assert g['descriptive_above_3_rms'] == [norm(sums[j]) > 9*null[j] for j in range(2)] == [False, False]
        if gi == 0: assert sums[3] == (N, 0)
        else: assert sums == [mul(chi[2], s) if gi == 1 else (-s[0], -s[1]) for s in G[0]]
        G.append(sums)
    for pr in f['permutations']:
        labels = {x['n']: x['assigned_label'] for x in pr['rows']}
        assert set(labels.values()) == set(range(1, q))
        assert all(labels[q-n] == q-d for n, d in labels.items()) and pr['complete'] and pr['shuffle_complete']
        for a in pr['assignments']:
            assert labels[a['n']] == a['label'] and labels[q-a['n']] == a['opposite_label']
        sums = [(0, 0)]*2; zeros = [0]*2
        for x in pr['rows']:
            assert x['complete'] and x['point'] == base[x['n']-1]['point']
            vals = cache[tuple(x['point'])]; w = conj(chi[x['assigned_label']])
            for j in range(2):
                sums[j] = add(sums[j], mul(vals[j], w)); zeros[j] += (vals[j] == (0, 0))
        for rec, s in zip(pr['sums'], sums):
            assert tuple(rec['pair']) == s and rec['denominator'] == N and rec['squared_magnitude_denominator'] == N*N and rec['squared_magnitude_numerator'] == norm(s)
        assert pr['zero_counts'] == zeros and pr['descriptive_above_3_rms'] == [norm(sums[j]) > 9*null[j] for j in range(2)] == [False, False]
    pref = 'p'+str(p)+'/'
    expected = 2*p+3*q+8*N+len(f['character']['prime_divisors_q_minus_1'])+9+3*(N//2+q+N)
    assert sum(v for k, v in r['storage_entries_by_table'].items() if k.startswith(pref)) == expected
    print(p, q, f['candidate_count'], G[0][:2], [norm(v) for v in G[0][:2]], null)
c = r['category_counts']
assert c['field_reductions'] == c['field_adds']+c['field_muls']+c['field_subs']+c['field_power_calls']
assert c['field_inverse_calls'] == c['field_power_calls'] == sum(4*f['q']-6 for f in r['fields'])
for name in ('character_screen.py', 'protocol.md', 'initial_results.json'):
    print(name, hashlib.sha256(Path('research/experiments/H014', name).read_bytes()).hexdigest())
assert r['source_sha256'] == hashlib.sha256(Path('research/experiments/H014/character_screen.py').read_bytes()).hexdigest()
print('PASS: saved-data-only audit; no character_screen import or curve/group recomputation')
