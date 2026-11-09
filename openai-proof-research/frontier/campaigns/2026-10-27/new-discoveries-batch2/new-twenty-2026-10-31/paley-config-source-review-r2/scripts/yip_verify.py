"""Independent exact check of the MathDB 355956 counterexample q = 5^8, d = 3.
Own GF(5^8) arithmetic (F_5[X]/(f), f = X^8+X^7+2X^6+2); no code shared with the author lane.
Usage: python3 -I yip_verify.py OUT.json"""
import json, sys, time, itertools
t0 = time.time(); p, n, d = 5, 8, 3; q = p ** n
F = [2, 0, 0, 0, 0, 0, 2, 1, 1]          # f coefficients, low degree first: 2 + 2X^6 + X^7 + X^8
def mul(a, b):
    r = [0] * (2 * n - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b): r[i + j] += x * y
    for k in range(2 * n - 2, n - 1, -1):  # reduce mod f (monic)
        c = r[k] % p
        if c:
            for j in range(n): r[k - n + j] -= c * F[j]
        r[k] = 0
    return tuple(v % p for v in r[:n])
def pw(a, e):
    r = (1,) + (0,) * (n - 1)
    while e:
        if e & 1: r = mul(r, a)
        a = mul(a, a); e >>= 1
    return r
ONE = (1,) + (0,) * (n - 1); X = (0, 1) + (0,) * (n - 2)
def el(*c): return tuple(list(c) + [0] * (n - len(c)))
def sub_const(a, c): return ((a[0] - c) % p,) + a[1:]
def frob_order(a):
    b = a
    for m in range(1, n + 1):
        b = pw(b, p)
        if b == a: return m
def factor(N):
    fs, k = [], 2
    while k * k <= N:
        while N % k == 0: fs.append(k); N //= k
        k += 1
    if N > 1: fs.append(N)
    return sorted(set(fs))
res = {}
# (0) congruence and r
res["q"] = q; res["q_mod_2d"] = (q - 1) % (2 * d)
res["admissible_r"] = [r for r in range(1, n + 1) if n % r == 0 and ((q - 1) // (p ** r - 1)) % d == 0]
res["r"] = max(res["admissible_r"])
# (1) f irreducible (Rabin): X^(5^8) = X and gcd condition via X^(5^4) != X on every proper factor; use degree of X
res["X_frobenius_order"] = frob_order(X)   # = 8 iff f irreducible (f has a root of exact degree 8 => irreducible of degree 8)
assert res["X_frobenius_order"] == 8
# (2) cubic character by direct exponentiation (independent of any log table)
E = (q - 1) // d
def is_cube_nonzero(a): return any(a) and pw(a, E) == ONE
res["minus_one_is_cube"] = is_cube_nonzero(el(p - 1))
res["F5_star_all_cubes"] = all(is_cube_nonzero(el(a)) for a in range(1, p))
x = el(0, 2, 4, 1)                       # 2θ + 4θ^2 + θ^3
res["x_coeffs"] = list(x); res["x_in_F5"] = any(x == el(a) for a in range(p))
res["x_minus_a_cubes"] = {a: is_cube_nonzero(sub_const(x, a)) for a in range(p)}
res["x_frobenius_degree"] = frob_order(x)
# (3) F5 + x F5 is a 25-clique (all 24 nonzero elements a + b x are cubes)
span = [tuple((a * (1 if i == 0 else 0) + b * x[i]) % p for i in range(n)) for a in range(p) for b in range(p)]
res["span_F5_xF5_is_clique_size25"] = all(is_cube_nonzero(v) for v in span if any(v))
# (4) larger subfields are not cliques: generators of F_25^*, F_625^* from a primitive element
N = q - 1; fs = factor(N); res["q_minus_1_prime_factors"] = fs
g = next(c for c in [X] + [el(a, 1) for a in range(1, p)] + [el(a, b, 1) for a in range(p) for b in range(p)]
         if all(pw(c, N // l) != ONE for l in fs))
res["primitive_element"] = list(g)
for m in (2, 4):
    h = pw(g, (q - 1) // (p ** m - 1)); res[f"F_{p**m}_generator_is_cube"] = is_cube_nonzero(h)
# (5) exhaustive count of extension vertices via a discrete-log table of g (cubic character = log mod 3)
logt = {}; cur = ONE
for k in range(q - 1): logt[cur] = k; cur = mul(cur, g)
assert cur == ONE and len(logt) == q - 1
def chi0(a): return a in logt and logt[a] % 3 == 0
ext = [a for a in itertools.product(range(p), repeat=n) if any(a[1:]) and all(chi0(sub_const(a, c)) for c in range(p))]
res["n_extension_vertices"] = len(ext); res["x_among_them"] = x in set(ext)
deg = {}
for a in ext: deg[frob_order(a)] = deg.get(frob_order(a), 0) + 1
res["extension_vertices_by_degree"] = deg
res["consistency_log_vs_power"] = all(chi0(sub_const(x, c)) == res["x_minus_a_cubes"][c] for c in range(p))
res["seconds"] = round(time.time() - t0, 2)
json.dump(res, open(sys.argv[1], "w"), indent=1, default=str); print(json.dumps(res, indent=1, default=str))
