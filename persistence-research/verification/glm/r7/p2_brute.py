# r7 p2_brute.py — ground truth for the mixed residual (M*).
# Families: 9n = 10^L + A*10^q + K  (one far digit), K = 9*S_low - 1,
# with (S_low, A) in the 10 surviving pairs, L > q >= 3, n = 2^t 3^a 7^w.
# Plus the {2,2,2} two-far variant: 9n = 10^L + 9*10^q1 + 9*10^q2 + K,
# S_low in {1, 10}, 3 <= q1 < q2 < L.
# A solution of the equation (10^L + ... + K is {2,3,7}-smooth) with L > q >= 3
# corresponds exactly to a family member: n = repunit(L) + S, no carries.
# Run: bash -c 'ulimit -v 3000000; python3 -I p2_brute.py [LMAX]'

import sys

def smooth237(x):
    for p in (2, 3, 7):
        while x % p == 0:
            x //= p
    return x == 1

def factors(x):
    r = []
    for p in (2, 3, 7):
        e = 0
        while x % p == 0:
            x //= p; e += 1
        r.append(e)
    return tuple(r), x

LMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
PAIRS = [(1, 9), (10, 9), (1, 18), (10, 18), (1, 27), (10, 27),
         (30, 27), (11, 9), (101, 9), (110, 9)]

pow10 = [10 ** i for i in range(LMAX + 2)]
out = {}
for S, A in PAIRS:
    K = 9 * S - 1
    sols = []
    for L in range(4, LMAX + 1):
        base = pow10[L] + K
        for q in range(3, L):
            X = base + A * pow10[q]
            if smooth237(X):
                t, a, w, cof = *factors(X)[0], factors(X)[1]
                sols.append((L, q, X // 9, factors(X)[0]))
    out[f"{S},{A}"] = sols
    print(f"S_low={S:>3} A={A:>2} (K={K:>3}): {len(sols)} solution(s)", flush=True)
    for L, q, n, fac in sols[:5]:
        print(f"   L={L} q={q} n={n} (t,a,w)={fac}")

# two-far {2,2,2}: S_low in {1, 10}, far digits 2,2
LF = min(LMAX, 400)
for S in (1, 10):
    K = 9 * S - 1
    sols = []
    for L in range(5, LF + 1):
        base = pow10[L] + K
        for q1 in range(3, L - 1):
            b2 = base + 9 * pow10[q1]
            for q2 in range(q1 + 1, L):
                if smooth237(b2 + 9 * pow10[q2]):
                    sols.append((L, q1, q2, (b2 + 9 * pow10[q2]) // 9))
    print(f"two-far S_low={S}: {len(sols)} solution(s) (L<={LF})")
    for s in sols[:5]:
        print("   ", s)
