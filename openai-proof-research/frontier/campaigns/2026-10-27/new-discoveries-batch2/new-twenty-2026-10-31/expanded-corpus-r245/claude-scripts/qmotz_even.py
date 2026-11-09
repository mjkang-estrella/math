"""Coefficient nonnegativity of even-shift q-Motzkin Hankel determinants (Conjecture A.4, MathDB 339078),
via the block identity; diagnostic coverage only.  usage: qmotz_even.py QMOTZ_PY SHIFTS NMAX"""
import importlib.util
import sys
import time

spec = importlib.util.spec_from_file_location('qm', sys.argv[1])
Q = importlib.util.module_from_spec(spec)
spec.loader.exec_module(Q)
shifts = [int(s) for s in sys.argv[2].split(',')]
NMAX = int(sys.argv[3])
t0 = time.time()
for r in shifts:
    bad = []
    done = 0
    for n in range(1, NMAX + 1):
        d = Q.block_det(n, r)
        if not d or any(x < 0 for x in d):
            bad.append(n)
        done = n
        if time.time() - t0 > 85:
            break
    print('shift', r, 'n<=', done, 'negative-or-zero cases', bad, round(time.time() - t0, 1), 's', flush=True)
