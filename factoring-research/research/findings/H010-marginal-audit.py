#!/usr/bin/env python3
"""Independent bitset replay of the frozen witness, not a second screen."""
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import time

P = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('h010_frozen', P/'H010-marginal-screen.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
manifest = json.loads((P/'H010-marginal-manifest.json').read_text())
cases = json.loads((P/'H010-marginal-cases.json').read_text())
assert [{k:v for k,v in c.items() if k != 'status'} for c in manifest['cases']] == cases
for key, filename in [('source_sha256', 'H010-marginal-screen.py'),
                      ('protocol_sha256', 'H010-marginal-prereg.md')]:
    assert hashlib.sha256((P/filename).read_bytes()).hexdigest() == manifest[key]
validation = json.loads((P/'H010-marginal-validation.json').read_text())
assert validation['source_sha256'] == manifest['source_sha256']
events = [json.loads(line) for line in (P/'H010-marginal-outcomes.jsonl').read_text().splitlines()]
started = {e['id'] for e in events if e['event'] == 'started'}
finished = {e['id']: e for e in events if e['event'] == 'finished'}
records = []
for case in cases:
    records.append(dict(case, **{k:v for k,v in finished.get(case['id'], {}).items()
                                if k not in ('id', 'event')},
                        final_status=finished[case['id']]['status'] if case['id'] in finished
                        else 'incomplete' if case['id'] in started else 'unstarted'))
(P/'H010-marginal-results.json').write_text(json.dumps(records, indent=2)+'\n')

start = time.monotonic()
replays = []
for record in records:
    if record['final_status'] not in ('complete', 'width_rejected'):
        continue
    C, variables, factors, wires = module.candidate(record['N'], record['a'], record['k'])
    adjacency = {v: 0 for v in variables}
    for scope, table in factors:
        mask = sum(1 << v for v in scope)
        for v in scope:
            adjacency[v] |= mask ^ (1 << v)
    initial = max((len(scope) for scope, _ in factors), default=0)
    max_output, max_bucket = initial, initial
    order = record.get('order', record.get('order_prefix'))
    for selected in order:
        scores = {}
        for v, mask in adjacency.items():
            d = mask.bit_count()
            degree_sum = 0
            scan = mask
            while scan:
                bit = scan & -scan
                u = bit.bit_length()-1
                degree_sum += (adjacency[u] & mask).bit_count()
                scan ^= bit
            scores[v] = d*(d-1)//2 - degree_sum//2
        best = min(adjacency, key=lambda v: (scores[v], v))
        assert selected == best
        mask = adjacency[selected]
        max_output = max(max_output, mask.bit_count())
        max_bucket = max(max_bucket, mask.bit_count()+1)
        if selected == order[-1] and record['final_status'] == 'width_rejected':
            assert sorted(v for v in adjacency if mask & (1 << v)) == record['witness_neighbors']
            assert scores[selected] == record['witness_fill']
        scan = mask
        while scan:
            bit = scan & -scan
            u = bit.bit_length()-1
            adjacency[u] = (adjacency[u] | mask) & ~((1 << u) | (1 << selected))
            scan ^= bit
        del adjacency[selected]
    assert max_bucket == record.get('width', record.get('width_lower_bound'))
    if record['final_status'] == 'complete':
        assert not adjacency
    # Verify each residual Boolean DAG assignment on this actually seen prefix.
    # This is finite function validation, not graph planning or tensor contraction.
    ket, bra, out, out2 = wires
    k, m = record['k'], record['m']
    for u in range(1 << k):
        for v in range(1 << k):
            values = C.evaluate([(u >> i)&1 for i in range(k)] +
                                [(v >> i)&1 for i in range(k)])
            assert module.readword(out, values) == pow(record['a'], u << (m-k), record['N'])
            assert module.readword(out2, values) == pow(record['a'], v << (m-k), record['N'])
    replays.append(dict(id=record['id'], checked_steps=len(order),
                        initial_max_factor=initial, max_bucket=max_bucket,
                        max_output_factor=max_output,
                        checked_input_pairs=1 << (2*k)))

# Exact symbolic prefix check, all histories. Polynomial coefficients indexed
# by powers of a formal 2^k-th root are compared, not approximated numerically.
symbolic = 0
for N in range(3, 16, 2):
    for a in range(1, N):
        if module.math.gcd(a, N) != 1:
            continue
        m = (N*N-1).bit_length()
        for k in range(m+1):
            t = m-k
            qk = 1 << k
            before, after = Counter(), Counter()
            for u in range(qk):
                for v in range(qk):
                    if pow(a, u << t, N) == pow(a, v << t, N):
                        after[(u-v) % qk] += 1
            # Grouped full sum; one copy for each low v, using actual pow values.
            for low in range(1 << t):
                values = [pow(a, (u << t)+low, N) for u in range(qk)]
                groups = {}
                for u, value in enumerate(values):
                    groups.setdefault(value, []).append(u)
                for indices in groups.values():
                    for u in indices:
                        for v in indices:
                            before[(u-v) % qk] += 1
            assert before == Counter({e:c*(1 << t) for e,c in after.items()})
            symbolic += 1  # equality for all histories s at once

print(json.dumps(dict(status='passed', source_sha256=manifest['source_sha256'],
                     protocol_sha256=manifest['protocol_sha256'],
                     cases=len(records), statuses=dict(Counter(r['final_status'] for r in records)),
                     witness_replays=replays,
                     symbolic_all_history_prefix_identities=symbolic,
                     elapsed_seconds=time.monotonic()-start), indent=2))
