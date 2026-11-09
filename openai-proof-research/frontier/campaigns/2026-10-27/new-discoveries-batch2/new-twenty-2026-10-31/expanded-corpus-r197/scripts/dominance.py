"""Merge chunk outputs of dumont.py and check Conjecture 5.3 (MathDB 345654).
usage: dominance.py N file1.json [file2.json ...]"""
import sys, json
from math import comb
N = int(sys.argv[1]); A = {}; B = {}; fa = set(); fb = set()
for f in sys.argv[2:]:
    d = json.load(open(f))
    assert d['N'] == N
    for w, acc, fs in (('a', A, fa), ('b', B, fb)):
        if w in d:
            assert not (fs & set(d['firsts'])), 'overlap'
            fs |= set(d['firsts'])
            for k, v in d[w].items():
                acc[int(k)] = acc.get(int(k), 0) + v
full = set(range(1, 2 * N + 1))
print('coverage a', fa == full, 'b', fb == full)
top = comb(N, 2)
print('totals', sum(A.values()), sum(B.values()))
print('top a,b', A.get(top), B.get(top), 'beyond top', [k for k in list(A) + list(B) if k > top])
ca = cb = 0; viol = []; slack = []
for m in range(top + 1):
    ca += A.get(m, 0); cb += B.get(m, 0)
    slack.append(ca - cb)
    if ca < cb: viol.append((m, ca, cb))
print('cumulative a-b:', slack)
print('violations:', viol)
print('a:', [A.get(k, 0) for k in range(top + 1)])
print('b:', [B.get(k, 0) for k in range(top + 1)])
