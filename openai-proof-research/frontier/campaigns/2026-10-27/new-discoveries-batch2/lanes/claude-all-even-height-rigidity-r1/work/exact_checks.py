"""Bounded EXACT (rational) checks for the partial statements in discovery.md.
Checks are illustrations/regression tests of proved statements, not proofs.
 C0  checker reproduces source all-even sets (Sect. 6.2, Lemma 6.3) and
     detects perturbations.
 C1  Prop A (two parallel planes): the pair (lex-min of bottom, lex-max of top)
     determines a singly-determined direction; n_S is |S|-1 there.
 C2  Prop B (two non-parallel planes, bottom part one-sided): the bi-order
     maximal cross pair is singly determined.
 C3  Prop C (products Q x H with c_g(H) odd): predicted direction is odd.
 C4  Lemma D witness: 3-layer single-swap modification of a centrally
     symmetric set; random non-planar instances always have odd directions,
     and the planar instance A_1 (source Lemma 6.3) is all-even.
"""
import sys, os, json, random
from fractions import Fraction as F
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lp import direction_counts, odd_directions, _prim
from selftest_data import SETS, Ak

rng = random.Random(20261030)
out = {}

# C0
c0 = {k: len(odd_directions(v)) for k, v in SETS.items()}
c0['S8_minus_point'] = len(odd_directions(SETS['S8'][:-1]))
c0['S8_moved_point'] = len(odd_directions(SETS['S8'][:-1] + [(0, 3)]))
assert all(c0[k] == 0 for k in SETS) and c0['S8_minus_point'] > 0 and c0['S8_moved_point'] > 0
out['C0'] = c0


def ncount(S, d):
    return direction_counts(S).get(_prim(d), len(S))


def pairs_with_dir(S, d):
    k = _prim(d)
    return [(p, q) for i, p in enumerate(S) for q in S[i + 1:] if _prim([b - a for a, b in zip(p, q)]) == k]


# C1: S in planes z=0 and z=1 (after affine normalisation), random rational data
c1 = []
for t in range(60):
    A = {(F(rng.randint(-4, 4)), F(rng.randint(-4, 4)), F(0)) for _ in range(rng.randint(1, 6))}
    B = {(F(rng.randint(-4, 4)), F(rng.randint(-4, 4)), F(1)) for _ in range(rng.randint(1, 6))}
    S = sorted(A | B)
    if len(S) % 2:
        continue
    a = min(A); b = max(B)
    d = [y - x for x, y in zip(a, b)]
    pr = pairs_with_dir(S, d)
    n = ncount(S, d)
    assert len(pr) == 1 and n == len(S) - 1, (S, d)
    c1.append(n % 2)
out['C1'] = {'instances_even_size': len(c1), 'all_odd_at_predicted_direction': all(c1)}


# C2: H1 = {z=0} with coords (x,y), H2 = {y=0} with coords (x,z), K = x-axis.
# S1 strictly on y>0 side; S2 arbitrary off K (both sides); optional points on K.
def biorder_key(mu, kappa):
    return (kappa, mu)  # (mu,kappa) compared: kappa first, then mu (bi-order on G^0)


c2 = []
for t in range(60):
    S1 = {(F(rng.randint(-3, 3)), F(rng.randint(1, 4)), F(0)) for _ in range(rng.randint(1, 5))}
    S2 = {(F(rng.randint(-3, 3)), F(0), F(rng.choice([-3, -2, -1, 1, 2, 3]))) for _ in range(rng.randint(1, 5))}
    S0 = {(F(rng.randint(-3, 3)), F(0), F(0)) for _ in range(rng.randint(0, 2))}
    S = sorted(S1 | S2 | S0)
    if len(S) % 2:
        continue
    pos = [b for b in S2 if b[2] > 0]
    if pos:
        # G^0 component: maximise kappa=z_b/y_a then mu=(x_b-x_a)/y_a
        best = max(((b[2] / a[1], (b[0] - a[0]) / a[1]), a, b) for a in S1 for b in pos)
    else:
        # all of S2 negative: component delta*theta(alpha^*) t; element (mu,kappa) with
        # kappa=|z_b|/y_a, mu=-(x_b-x_a)/y_a after theta; maximise in bi-order
        best = max(((-b[2] / a[1], -(b[0] - a[0]) / a[1]), a, b) for a in S1 for b in S2)
    _, a, b = best
    d = [y - x for x, y in zip(a, b)]
    pr = pairs_with_dir(S, d)
    n = ncount(S, d)
    assert len(pr) == 1 and n == len(S) - 1, (S, a, b, pr)
    c2.append(n % 2)
out['C2'] = {'instances_even_size': len(c2), 'all_odd_at_predicted_direction': all(c2)}

# C3: products Q x H, H with c_g(H) odd; direction (D/g * u, 1), u unit diameter dir.
# Use integer-friendly data: choose Q with diameter along an axis so D is rational.
c3 = []
for t in range(40):
    Q = {(rng.randint(0, 6), rng.randint(0, 3)) for _ in range(rng.randint(2, 6))}
    Q.add((0, 0)); Q.add((9, 0))  # diameter pair along x-axis, length 9 (others shorter)
    Q = sorted(Q)
    if max((a[0] - b[0]) ** 2 + (a[1] - b[1]) ** 2 for a in Q for b in Q) != 81:
        continue
    H = rng.choice([[0, 1], [0, 1, 3], [0, 2, 3, 7], [0, 1, 4]])
    gaps = sorted({abs(x - y) for x in H for y in H if x != y})
    g = gaps[0]
    cg = sum(1 for x in H if x + g in H)
    if cg % 2 == 0:
        continue
    S = [(F(x), F(y), F(h)) for (x, y) in Q for h in H]
    if len(S) % 2:
        continue
    d = [F(9, g), F(0), F(1)]
    n = ncount(S, d)
    c3.append((n % 2, len(S) - n == cg))
assert all(a and b for a, b in c3)
out['C3'] = {'instances': len(c3), 'odd_and_drop_equals_cg': all(a and b for a, b in c3)}


# C4: B = B1 at z=1, B0 row on x-axis at z=0 (symmetric, origin excluded), B-1=-B1;
# S = B - q + p with p at height 2.  Lemma D: line-all-even forces planarity.
def lemmaD(B1, B0, q, pbar):
    Bm1 = [(-x, -y) for (x, y) in B1]
    S = [(F(x), F(y), F(1)) for x, y in B1] + [(F(x), F(0), F(0)) for x in B0 if x != q] + \
        [(F(x), F(y), F(-1)) for x, y in Bm1] + [(F(pbar[0]), F(pbar[1]), F(2))]
    return S


A1 = Ak(1)  # planar instance: rows y=-1,0,1 and p=(-1,2); embed with z=y (plane)
planar = [(F(x), F(y), F(y)) for x, y in A1]
c4 = {'A1_planar_embedding_odd_dirs': len(odd_directions(planar))}
assert c4['A1_planar_embedding_odd_dirs'] == 0
nonplanar_odd = []
for t in range(40):
    B1 = {(rng.randint(-5, 5), rng.choice([1, 2])) for _ in range(rng.randint(2, 6))}
    m = rng.randint(1, 4)
    B0 = [2 * i - 1 for i in range(-m + 1, m + 1)]
    q = rng.choice(B0)
    pbar = (rng.randint(-5, 5), rng.choice([2, 3, 4]))
    S = lemmaD(sorted(B1), B0, q, pbar)
    ys = {s[1] - s[2] * F(pbar[1], 2) for s in S}
    if len(ys) == 1:
        continue  # planar (y = c z) instance, excluded by hypothesis
    nonplanar_odd.append(len(odd_directions(S)))
assert all(k > 0 for k in nonplanar_odd)
c4['nonplanar_instances'] = len(nonplanar_odd)
c4['min_odd_dirs_nonplanar'] = min(nonplanar_odd)
out['C4'] = c4
print(json.dumps(out, indent=1))
