import random, json, glob, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from e_enum import *
random.seed(7)
# 1. formula 9n = 10^L + K + sum A_i 10^q_i  (low positions exact), on random digit strings
for _ in range(20000):
    L = random.randint(4, 40)
    digs = [random.choice((1, 1, 1, 2, 3, 4, 6, 7, 8, 9)) for _ in range(L)]      # digs[p] = digit at position p
    n = sum(d * 10 ** p for p, d in enumerate(digs))
    S_low = sum((digs[p] - 1) * 10 ** p for p in range(3))
    rhs = 10 ** L + 9 * S_low - 1 + sum(9 * (digs[p] - 1) * 10 ** p for p in range(3, L))
    assert 9 * n == rhs
print('formula ok on 20000 random strings')
# 2. R40 by direct enumeration, mod 40 and mod 1000
D40 = {(2 ** i * 3 ** j * 7 ** k) % 40 for i in range(0, 60) for j in range(0, 60) for k in range(0, 60)}
assert D40 == R40, (sorted(D40), sorted(R40))
D1000 = {(2 ** i * 3 ** j * 7 ** k) % 1000 for i in range(0, 120) for j in range(0, 100) for k in range(0, 100)}
assert D1000 == R1000
print('R40 (%d residues) and R1000 (%d residues) agree with direct enumeration' % (len(R40), len(R1000)))
# 3. n mod 1000 = 111 + S_low for L>=3 (no carry)  <=> digits (d-1)+1 <= 9
assert all(1 + (d - 1) <= 9 for d in DIG)
# 4. parity-dead summary by (S_low mod 40) pattern, and a spot check of the lemma S_low=0
print('S_low=0 dead:', (111 % 40) not in R40, '; 111 mod 40 =', 111 % 40)
# 5. qmin spread
q = []; 
for f in glob.glob('../glm/L2c/cert_t*.jsonl'):
    m = json.loads(open(f).readline()); q.append((m['qmin'], m['dim']))
print('max qmin over all C certs:', max(q), '; dim1 certs max qmin', max(x for x, d in q if d == 1))
