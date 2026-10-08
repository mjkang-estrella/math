"""Independent reference execution of frozen Markdown rows, NOT Lean execution.
Only temporary review evidence is written. The test suite uses at most 1M
setup/guest model events. It proves no generic refinement or complexity claim.
"""
import collections
import hashlib
import json
import re

GRAPH = 'research/proposals/W018-query-instruction-graphs.md'
EXPECTED_HASH = '08b5befa350dcd0d7f4b98932cb59a0ba3faca54683e911265af3b185b48cf26'
text = open(GRAPH).read()
assert hashlib.sha256(text.encode()).hexdigest() == EXPECTED_HASH
parts = [
    text.split('## Common prefix:')[1].split('## Sequential sorted search:')[0],
    text.split('## Sequential sorted search:')[1].split('## Binary indexed search:')[0],
    text.split('## Binary indexed search:')[1].split('## Prefix end state')[0],
]
tables = []
for part in parts:
    rows = [(int(pc), ins.split()) for pc, ins in
            re.findall(r'^\|\s*(\d+)\s*\|\s*`([^`]+)`\s*\|', part, re.M)]
    tables.append(rows)
common, linear, binary = tables
programs = {'linear': dict(common + linear), 'binary': dict(common + binary)}
arity = {'const': 3, 'mov': 3, 'add': 4, 'sub': 4, 'mul': 4, 'divmod': 5,
         'eq': 4, 'lt': 4, 'load': 3, 'store': 3, 'jump': 1, 'branch': 3, 'halt': 0}
regpos = {'const': [0], 'mov': [0, 1], 'add': [0, 1, 2], 'sub': [0, 1, 2],
          'mul': [0, 1, 2], 'divmod': [0, 1, 2, 3], 'eq': [0, 1, 2],
          'lt': [0, 1, 2], 'load': [0, 1], 'store': [0, 1], 'jump': [],
          'branch': [0], 'halt': []}
dests = {'const': [0], 'mov': [0], 'add': [0], 'sub': [0], 'mul': [0],
         'divmod': [0, 1], 'eq': [0], 'lt': [0], 'load': [0], 'store': [],
         'jump': [], 'branch': [], 'halt': []}
slots = {'W', 'L', 'B', 'A', 'A+1', 'A+2'}
for name, prog in programs.items():
    assert set(prog) == set(range(110 if name == 'linear' else 115))
    for pc, (op, *args) in prog.items():
        assert len(args) == arity[op]
        for i in regpos[op]:
            assert 0 <= int(args[i]) < 32
        for i in dests[op]:
            assert int(args[i]) != 0
        targets = [] if op == 'halt' else args[1:] if op == 'branch' else args[-1:]
        assert all(0 <= int(t) < len(prog) for t in targets)
        if pc >= 86:
            assert all(int(t) > 86 for t in targets)
        if op == 'const':
            assert args[1] in slots or args[1] in {'0', '1', '2'}
        if op == 'divmod':
            assert args[0] != args[1]


def layout(W, m, k):
    U = 1 << W
    L = 2*W + m*(k+W) + k
    B = L+2
    A = B+2*m
    M = A+4
    I = 32+M+L
    F = I+256*(L+4*m+32)
    return U, L, B, A, M, I, F


def admits(W, m, k):
    U, L, B, A, M, I, F = layout(W, m, k)
    if not (W > 0 and k <= W and M <= U and m < U and k < U):
        return False
    lits = {'W': W, 'L': L, 'B': B, 'A': A, 'A+1': A+1, 'A+2': A+2}
    for prog in programs.values():
        if len(prog) > U:
            return False
        for pc, (op, *args) in prog.items():
            for i, v in enumerate(args):
                if i not in regpos[op] and not 0 <= (lits[v] if v in lits else int(v)) < U:
                    return False
    return True


witnesses = [(7, 0, 0), (7, 0, 7), (7, 1, 0), (7, 1, 7),
             (7, 2, 1), (7, 3, 2), (7, 6, 7), (7, 12, 0)]
assert all(admits(*s) for s in witnesses)
assert all(not admits(*s) for s in [(7, 7, 7), (7, 13, 0), (6, 0, 0)])
admission_cases = 0
for W in range(13):
    for k in range(W+2):
        for m in range(30):
            U, L, B, A, M, I, F = layout(W, m, k)
            expected = W >= 7 and k <= W and M <= U and m < U and k < U
            assert admits(W, m, k) == expected
            admission_cases += 1

events = 0
runs = 0
prefixes = 0
calls = 0


def bits(w, n):
    return [(n >> j) & 1 for j in range(w)]


def run(name, W, k, entries, x, fuel=None):
    global events, runs, prefixes, calls
    calls += 1
    m = len(entries)
    assert admits(W, m, k)
    assert all(0 <= a < (1 << k) and 0 <= v < (1 << W) for a, v in entries)
    assert all(entries[j][0] <= entries[j+1][0] for j in range(m-1))
    assert 0 <= x < (1 << k)
    U, L, B, A, M, I, F = layout(W, m, k)
    fuel = F if fuel is None else fuel
    initial = fuel
    src = bits(W, m)+bits(W, k)+[b for a, v in entries for b in bits(k, a)+bits(W, v)]+bits(k, x)
    assert len(src) == L
    regs = [None]*32
    heap = [None]*M
    trace = []
    pc = 0

    def charge(kind):
        global events
        nonlocal fuel
        assert fuel > 0
        fuel -= 1
        trace.append(kind)
        events += 1
        assert events <= 1000000

    for r in range(32):
        if not fuel:
            return 'setup', regs, heap, pc, trace, fuel, None
        charge('clearRegister')
        regs[r] = 0
    for a in range(M):
        if not fuel:
            return 'setup', regs, heap, pc, trace, fuel, None
        charge('clearHeap')
        heap[a] = 0
    for i, b in enumerate(src):
        if not fuel:
            return 'setup', regs, heap, pc, trace, fuel, None
        charge('copyInput')
        heap[i] = b
    prog = programs[name]
    lits = {'W': W, 'L': L, 'B': B, 'A': A, 'A+1': A+1, 'A+2': A+2}
    boundary = None
    probes = 0
    while fuel:
        if pc == 86:
            assert boundary is None
            c = L-k
            lastbit = x % 2 if k else entries[-1][1] % 2 if m else 0
            expected = [0, 1, 2, W, m, k, L, k, c, x, lastbit, L, B, A, m,
                        entries[-1][0] if m else 0, entries[-1][1] if m else 0,
                        x, 0, 0, 0, 0, 0, 0, 0, A+2, L, c, 0, 0, 0, 0]
            assert regs == expected, (name, W, k, entries, x, 'registers', regs, expected)
            assert heap == src+[0, 0]+[n for e in entries for n in e]+[m, k, x, 0]
            prefix = trace[I:]
            cc = collections.Counter(prefix)
            expected_counts = {'const': 9, 'mov': 12*m+19, 'add': L+5*m+3,
                               'sub': L, 'mul': L+m, 'lt': L+3*m+4,
                               'branch': L+3*m+4, 'load': L, 'store': 2*m+3}
            assert cc == collections.Counter(expected_counts), (cc, expected_counts)
            assert len(prefix) == 6*L+26*m+42
            boundary = (len(trace), tuple(prefix), tuple(regs), tuple(heap))
            prefixes += 1
        assert pc in prog, (name, 'invalid PC', pc)
        op, *raw = prog[pc]
        a = [lits.get(v, int(v) if v.isdigit() else None) for v in raw]
        old = regs[:]
        charge(op)
        if op == 'halt':
            runs += 1
            assert heap[:L] == src and regs[0] == 0 and heap[A+3] == 0
            flag, payload = heap[L:L+2]
            matches = [j for j, e in enumerate(entries) if e[0] == x]
            assert flag == bool(matches)
            assert any(entries[j][1] == payload for j in matches) if matches else payload == 0
            if name == 'linear' and matches:
                assert payload == entries[matches[0]][1]
            if name == 'binary':
                lo, hi = 0, m
                expected_probe = 0
                expected_payload = None
                while lo < hi:
                    mid = lo+(hi-lo)//2
                    expected_probe += 1
                    if entries[mid][0] == x:
                        expected_payload = entries[mid][1]
                        break
                    if entries[mid][0] < x:
                        lo = mid+1
                    else:
                        hi = mid
                assert probes == expected_probe
                assert payload == (expected_payload if expected_payload is not None else 0)
            search = len(trace)-boundary[0]
            if name == 'linear':
                expected_search = 10*probes+7 if flag or (probes and entries[probes-1][0] > x) else 10*m+10
            else:
                expected_search = 13*probes+8 if flag else 13*probes+11
            assert search == expected_search, (name, entries, x, probes, search, expected_search)
            assert probes <= m and len(trace) <= I+6*L+39*m+53 <= F
            assert initial == len(trace)+fuel
            return 'halt', regs, heap, pc, trace, fuel, boundary
        if op == 'const':
            d, v, t = a
            regs[d] = v
        elif op == 'mov':
            d, b, t = a
            regs[d] = old[b]
        elif op in ['add', 'sub', 'mul', 'eq', 'lt']:
            d, b, c, t = a
            v = old[b]+old[c] if op == 'add' else old[b]-old[c] if op == 'sub' else old[b]*old[c] if op == 'mul' else int(old[b] == old[c]) if op == 'eq' else int(old[b] < old[c])
            assert 0 <= v < U, (name, pc, op, old[b], old[c])
            regs[d] = v
            if op == 'eq':
                probes += 1
        elif op == 'divmod':
            d, e, b, c, t = a
            assert old[c] != 0
            regs[d], regs[e] = divmod(old[b], old[c])
        elif op == 'load':
            d, b, t = a
            assert 0 <= old[b] < M
            regs[d] = heap[old[b]]
        elif op == 'store':
            b, c, t = a
            assert L <= old[b] < M
            heap[old[b]] = old[c]
        elif op == 'branch':
            b, t0, t1 = a
            t = t0 if old[b] == 0 else t1
        elif op == 'jump':
            t, = a
        else:
            raise AssertionError(op)
        assert all(0 <= v < U for v in regs)
        pc = t
    return 'guest', regs, heap, pc, trace, fuel, boundary


cases = []
# Complete data domains for these selected profiles: all payloads and queries.
for k in [0, 7]:
    for x in range(1 << k):
        cases.append((7, k, [], x))
for payload in range(128):
    cases.append((7, 0, [(0, payload)], 0))
# Targeted boundary/duplicate/absence cases; these domains are NOT exhaustive.
for k, keys in [(7, [0]), (7, [127]), (1, [0, 0]), (1, [1, 1]), (2, [0, 2, 2]),
                (7, [0, 1, 63, 64, 126, 127]), (0, [0]*12)]:
    for variant in [0, 1]:
        entries = [(a, (127 if (j+variant) % 2 else 0)) for j, a in enumerate(keys)]
        for x in sorted({0, (1 << k)-1, *keys, *[v for v in [1, 2, 62, 63, 64, 65, 126] if v < (1 << k)]}):
            cases.append((7, k, entries, x))
for case in cases:
    left = run('linear', *case)
    right = run('binary', *case)
    assert left[-1][1:] == right[-1][1:]
# Fresh fuel precedence and terminal stability at an empty-table instance.
case = (7, 0, [], 0)
U, L, B, A, M, I, F = layout(7, 0, 0)
for name in programs:
    full = run(name, *case)
    used = len(full[4])
    prefix = 6*L+42
    for fuel in [0, I-1, I, I+1, I+prefix, used-1, used, used+9]:
        out = run(name, *case, fuel=fuel)
        if fuel < I:
            assert out[0] == 'setup'
        elif fuel < used:
            assert out[0] == 'guest'
        else:
            assert out[0] == 'halt' and out[1:5] == full[1:5] and out[5] == fuel-used

results = {
    'scope': 'Independent Python reference execution of Markdown rows; NOT Lean execution/refinement or generic proof',
    'graph_sha256': EXPECTED_HASH,
    'static_instruction_counts': {'common': len(common), 'linear': len(programs['linear']), 'binary': len(programs['binary'])},
    'admission_witnesses_W_m_k': witnesses,
    'bounded_admission_equivalence_cases': admission_cases,
    'exhaustive_data_profiles_W_m_k': [[7, 0, 0], [7, 0, 7], [7, 1, 0]],
    'paired_datasets': len(cases),
    'total_reference_calls': calls,
    'halting_reference_calls': runs,
    'prefix_checks': prefixes,
    'total_setup_and_guest_model_events': events,
    'event_limit': 1000000,
    'verdict': 'PASS: all assertions; no failed test',
}
with open('/tmp/W018_graph_review_results.json', 'w') as f:
    json.dump(results, f, indent=2)
    f.write('\n')
print(json.dumps(results, indent=2))
