# r8 taskB.py — bounded attack on the 9 residual two-far {2,2,2} S_low=1 classes
# (hard_3d_S1.json, classes (L,q1,q2) mod M = 2*3^7*7^5 = 73513818, a >= 9 and
# w >= 6 both unbounded).  Equation: 2^3 3^a 7^w = 10^L + 9*10^q1 + 9*10^q2 + 8.
# Attempts:
#   (1) recompute signatures;                      (4) wide aux-prime region scan < 100000;
#   (2) pin vacuity (K/2^t0 = 1);                  (5) T0 primes with d | M;
#   (3) ladder persistence to depth 2*3^10*7^10
#       (Hensel-style: on-ladder child must persist; if it ever dies, residual killed).
# Run: bash -c 'ulimit -v 3000000; python3 -I taskB.py'
import json, math, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_cert2d as G

K = 8
raw = json.load(open("hard_3d_S1.json"))
classes = [tuple(c[:3]) for c in raw]
M = 2 * 3**7 * 7**5
assert all(len(c) == 3 for c in classes)
assert all(c == (c[0] % M, c[1] % M, c[2] % M) for c in classes), "class format"

def sig3(L, q1, q2, k3, k7):
    j, i = k3, k7
    m3 = 3 ** (j + 2)
    X = (pow(10, L, m3) + 9 * pow(10, q1, m3) + 9 * pow(10, q2, m3) + K) % m3
    a = (j + 2, None) if X == 0 else (G.vp(X, 3), G.vp(X, 3))
    m7 = 7 ** (i + 1)
    Y = (pow(10, L, m7) + 9 * pow(10, q1, m7) + 9 * pow(10, q2, m7) + K) % m7
    w = (i + 1, None) if Y == 0 else (G.vp(Y, 7), G.vp(Y, 7))
    return a, w

print("== (1) signatures at M = 2*3^7*7^5 ==", flush=True)
for c in classes:
    a, w = sig3(*c, 7, 5)
    print("  class", c, "a =", a, "w =", w)

print("== (2) pin vacuity: K/2^t0 ==", K // 8, "(=1, in every subgroup -> vacuous, as r7 found)", flush=True)

print("== (3) ladder persistence: deepen x3 then x7 on all three coordinates ==", flush=True)

def deepen(cur, mult):
    # cur: list of ((L,q1,q2) mod Mcur, k3, k7); step Mcur -> Mcur*mult, keep on-ladder children
    out = []
    for ((L, q1, q2), k3, k7) in cur:
        Mcur = 2 * 3**k3 * 7**k7
        Mn = Mcur * mult
        kept = 0
        for s in range(mult):
            cL, cq1, cq2 = (L + s * Mcur) % Mn, (q1 + s * Mcur) % Mn, (q2 + s * Mcur) % Mn
            a, w = sig3(cL, cq1, cq2, k3 + (1 if mult == 3 else 0), k7 + (1 if mult == 7 else 0))
            onladder = (a[1] is None) if mult == 3 else (w[1] is None)
            if onladder:
                out.append(((cL, cq1, cq2), k3 + (1 if mult == 3 else 0), k7 + (1 if mult == 7 else 0)))
                kept += 1
        if kept == 0:
            return None, ((L, q1, q2), k3, k7), mult
    return out, None, None

cur = [(c, 7, 5) for c in classes]
for rnd in range(1, 5):
    cur, died, mult = deepen(cur, 3)
    if cur is None:
        print(f"  round {rnd} x3: LADDER DIED for class {died} -> residual killable!"); break
    cur, died, mult = deepen(cur, 7)
    if cur is None:
        print(f"  round {rnd} x7: LADDER DIED for class {died} -> residual killable!"); break
    M = 2 * 3**cur[0][1] * 7**cur[0][2]
    print(f"  round {rnd}: {len(cur)} classes persist at modulus 2*3^{cur[0][1]}*7^{cur[0][2]} = {M}", flush=True)
else:
    print("  ladders persist indefinitely (as expected from the lifting lemma); no finite kill")

print("== (4)+(5) wide aux-prime scan, all primes < 100000, per class ==", flush=True)
PR = [q for q in G.PRIMES if q < 100000]
t0 = 3
for ci, c in enumerate(classes):
    L, q1, q2 = c
    print("   scanning class", c, flush=True)
    killed_by = None
    ncombos = 0
    for p in PR:
        d = G.ORD10[p]
        g = math.gcd(M, d)
        nc = (d // g) ** 3
        if nc > 4096:
            continue
        inv2 = pow(pow(2, t0, p), -1, p)
        o3, o7 = G.O3[p], G.O7[p]
        e = o3 * o7 // math.gcd(o3, o7)
        alive = False
        ncombos += 1
        for ggL in range(L % g, d, g):
            for gg1 in range(q1 % g, d, g):
                for gg2 in range(q2 % g, d, g):
                    T = (pow(10, ggL, p) + 9 * pow(10, gg1, p) + 9 * pow(10, gg2, p) + K) * inv2 % p
                    if T != 0 and pow(T, e, p) == 1:
                        alive = True
                        break
                if alive: break
            if alive: break
        if not alive:
            killed_by = p
            break
    print(f"  class {c}: {'KILLED by prime ' + str(killed_by) if killed_by else 'no kill among ' + str(ncombos) + ' usable primes (<100000)'}")

print("== T0 check: primes p | RHS on a whole class (d = ord_p(10) | M) ==")
any_t0 = False
for c in classes:
    for p in PR:
        d = G.ORD10[p]
        if M % d == 0 and (pow(10, c[0], p) + 9 * pow(10, c[1], p) + 9 * pow(10, c[2], p) + K) % p == 0:
            print("  class", c, "T0-killed by", p); any_t0 = True
if not any_t0:
    print("  none")
