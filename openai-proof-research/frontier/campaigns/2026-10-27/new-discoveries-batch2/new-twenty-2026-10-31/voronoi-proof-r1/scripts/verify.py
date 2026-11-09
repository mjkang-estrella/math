# Independent verification bundle (exact integers).
#  A: (3,2,2,2,2,2,2), n=15: every player's score = 1/8 (direct), and for EVERY deviation shape of player 0 the
#     direct brute-force score equals the convolution value; equilibrium decided by both.
#  B: (4,3,3,3,3,3,3), n=22: convolution over all 2^22 targets; direct brute force at all |c|<=1 shapes,
#     the best 10 shapes and 15 random shapes.
#  C: failures: uniform t=2,3 (n=14,21) and (5,5,5,1,0,0,0) (n=16): profitable target found by convolution,
#     confirmed by direct brute force at that target.
import sys; sys.path.insert(0, 'scripts')
from vk import *
import itertools, random, time, json
random.seed(7); out = {}
def rep(m, c):
    v = 0; off = 0
    for f in range(7):
        for j in range(c[f]): v |= 1 << (off + j)
        off += m[f]
    return v
def shape_of(m, v):
    c = []; off = 0
    for f in range(7):
        c.append(sum((v >> (off + j)) & 1 for j in range(m[f]))); off += m[f]
    return tuple(c)
t0 = time.time()
m = (3, 2, 2, 2, 2, 2, 2); n = sum(m); P = positions(m)
for i in range(8):
    oth = [P[j] for j in range(8) if j != i]
    assert frac(score_brute(n, oth, P[i]), n) == Fraction(1, 8)
oth = P[1:]; tab = voter_table(n, oth); S = scores_all(n, oth)
shapes = list(itertools.product(*[range(k + 1) for k in m])); mx = Fraction(0)
for c in shapes:
    v = rep(m, c); b = score_brute(n, oth, v, tab); assert b == S[v]
    if c != (0,) * 7: mx = max(mx, frac(b, n))
out['A'] = {'m': m, 'n': n, 'all_players_score_1_8': True, 'shapes_checked_brute_eq_conv': len(shapes), 'max_deviation_score': str(mx), 'equilibrium': mx < Fraction(1, 8)}
print('A', out['A'], round(time.time() - t0, 1), flush=True)
m = (4, 3, 3, 3, 3, 3, 3); n = sum(m); P = positions(m); oth = P[1:]
S = scores_all(n, oth); tab = voter_table(n, oth)
order = np.argsort(-S)[:400]
top = []
for v in order:
    c = shape_of(m, int(v))
    if c not in top and c != (0,)*7: top.append(c)
    if len(top) == 10: break
chk = [c for c in itertools.product(*[range(k + 1) for k in m]) if sum(c) <= 1] + top + [tuple(random.randint(0, k) for k in m) for _ in range(15)]
for c in chk:
    v = rep(m, c); assert score_brute(n, oth, v, tab) == S[v], c
mx = frac(np.max(S[1:]), n)
out['B'] = {'m': m, 'n': n, 'brute_checked_shapes': len(chk), 'max_deviation_score': str(mx), 'max_x8': float(mx * 8), 'argmax_shape': shape_of(m, int(np.argmax(S[1:]) + 1)), 'equilibrium': mx < Fraction(1, 8),
            'score_at_0': str(frac(S[0], n))}
print('B', out['B'], round(time.time() - t0, 1), flush=True)
for m in [(2,) * 7, (3,) * 7, (5, 5, 5, 1, 0, 0, 0)]:
    n = sum(m); P = positions(m); oth = P[1:]
    S = scores_all(n, oth); v = int(np.argmax(S)); tab = voter_table(n, oth)
    b = score_brute(n, oth, v, tab); assert b == S[v]
    out['C' + str(m)] = {'m': m, 'n': n, 'best_target_shape': shape_of(m, v), 'best_score': str(frac(b, n)), 'x8': float(frac(b, n) * 8), 'equilibrium': frac(b, n) <= Fraction(1, 8)}
    print('C', out['C' + str(m)], round(time.time() - t0, 1), flush=True)
open('verify-results.json', 'w').write(json.dumps(out, indent=1, default=str) + '\n')
