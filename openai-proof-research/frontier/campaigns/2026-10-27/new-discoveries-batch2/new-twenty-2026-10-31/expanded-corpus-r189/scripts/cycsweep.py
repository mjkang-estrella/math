"""Sweep Archer-Lauderdale Conjecture (complementary signature, MathDB 333370).
usage: cycsweep.py K NMIN NMAX OUTJSON
Computes c_sigma(n) for every sigma in {+,-}^K (one representative per reversal
class; c_sigma = c_{sigma^r} by the source's Prop. 2.7 / [ArcherElizalde Prop 2.7])
and n in [NMIN, NMAX]; appends results to OUTJSON (dict keyed 'sigma|n').
"""
import sys, json, itertools, pathlib, time
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from cycgrid import count

K, nmin, nmax, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), pathlib.Path(sys.argv[4])
data = json.loads(out.read_text()) if out.exists() else {}
reps = sorted({min(''.join(s), ''.join(s)[::-1]) for s in itertools.product('+-', repeat=K)})
t0 = time.time()
for n in range(nmin, nmax + 1):
    for s in reps:
        key = f'{s}|{n}'
        if key not in data:
            data[key] = count(s, n)
    out.write_text(json.dumps(data, indent=0, sort_keys=True))
    print('done n', n, 'elapsed', round(time.time() - t0, 1), flush=True)
comp = lambda s: ''.join('+' if c == '-' else '-' for c in s)
rep = lambda s: min(s, s[::-1])
bad = []
for s in reps:
    c = rep(comp(s))
    for n in range(1, nmax + 1):
        a, b = data.get(f'{s}|{n}'), data.get(f'{c}|{n}')
        if a is not None and b is not None and a != b:
            bad.append((s, c, n, n % 4, a, b))
print('mismatches (sigma, comp, n, n mod 4, c_sigma, c_comp):')
for x in sorted(set(tuple(sorted(x[:2])) + x[2:] for x in bad)):
    print(' ', x)
