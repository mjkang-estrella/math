"""Deeper analysis for MathDB 375237 / Ward Conjecture (arXiv:1606.04029).

For each triple S=(a,b,c), 0<a<b<c, c!=a+b:
  - exact minimal period m and preperiod via state-cycle detection;
  - Ward gcd check: m == gcd{s_i+s_j : (s_i+s_j) % m == 0};
  - win/lose sequence w (w=1 iff g!=0) minimal eventual period m_w;
  - which sums m divides.

Also: enumerate ALL solutions G: Z_L -> {0,1,2,3} of
      G(x) = mex{G[(x-a)%L], G[(x-b)%L], G[(x-c)%L]}
and report the minimal periods of solutions (tests whether "every periodic
solution has period dividing a pairwise sum" is true or false).
"""
import sys, json
from itertools import product


def analyze(S, N):
    a, b, c = S
    moves = (a, b, c)
    g = [0] * (N + 1)
    for n in range(1, min(c - 1, N) + 1):
        s = set()
        for mv in moves:
            if mv <= n:
                s.add(g[n - mv])
        i = 0
        while i in s:
            i += 1
        g[n] = i
    seen = {}
    for n in range(c - 1, N):
        st = tuple(g[n - c + 1:n + 1])
        if st in seen:
            start = seen[st]
            L = n - start
            cyc = g[start:n + 1]
            m = L
            for p in range(1, L + 1):
                if L % p == 0 and all(cyc[i] == cyc[i + p] for i in range(L - p)):
                    m = p
                    break
            div = [i for i in range(0, n - m + 1) if g[i] != g[i + m]]
            pre = (max(div) + 1) if div else 0
            return {"preperiod": pre, "min_period": m, "cycle": cyc[:L],
                    "cycle_start": start, "valid_upto": n, "g": g}
        seen[st] = n
        gn1 = n + 1
        s = set()
        for mv in moves:
            if mv <= gn1:
                s.add(g[gn1 - mv])
        i = 0
        while i in s:
            i += 1
        g[gn1] = i
    return None


def min_period_of(seq):
    n = len(seq)
    for p in range(1, n + 1):
        if n % p == 0 and all(seq[i] == seq[i + p] for i in range(n - p)):
            return p
    return n


def w_min_period(S, N):
    a, b, c = S
    g = [0] * (N + 1)
    for n in range(1, N + 1):
        s = set()
        for mv in (a, b, c):
            if mv <= n:
                s.add(g[n - mv])
        i = 0
        while i in s:
            i += 1
        g[n] = i
    w = [1 if x else 0 for x in g]
    # exact: state = window of c consecutive w values in {0,1}^c
    seen = {}
    for n in range(c - 1, N):
        st = tuple(w[n - c + 1:n + 1])
        if st in seen:
            start = seen[st]
            L = n - start
            cyc = w[start:n + 1]
            return min_period_of(cyc)
        seen[st] = n
        gn1 = n + 1
        w[gn1] = 1 if any(mv <= gn1 and g[gn1 - mv] == 0 for mv in (a, b, c)) else 0
    return None


def enumerate_solutions(S, L, cap=200000):
    """All G: Z_L -> {0..3} with G(x)=mex{G[x-a],G[x-b],G[x-c]} (mod L).
    Brute force for small L; returns list of minimal periods of solutions."""
    a, b, c = S
    if 4 ** L > cap * 4:
        return None
    res = []
    for tup in product(range(4), repeat=L):
        ok = True
        for x in range(L):
            vals = {tup[(x - a) % L], tup[(x - b) % L], tup[(x - c) % L]}
            i = 0
            while i in vals:
                i += 1
            if tup[x] != i:
                ok = False
                break
        if ok:
            res.append(min_period_of(tup))
    return res


def main():
    mode = sys.argv[1]
    if mode == "solutions":
        a, b, c, Lmax = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
        S = (a, b, c)
        sums = (a + b, b + c, c + a)
        out = []
        for L in range(1, Lmax + 1):
            sols = enumerate_solutions(S, L)
            if sols is None:
                continue
            bad = sorted({p for p in sols if all(p > s or s % p for s in sums)})
            allp = sorted(set(sols))
            out.append({"L": L, "n_solutions": len(sols),
                        "min_periods": allp,
                        "bad_min_periods": bad})
        print(json.dumps({"S": list(S), "sums": list(sums), "by_L": out}, indent=1))
        return

    B = int(sys.argv[2])
    N = 4000
    out = {"scanned": 0, "inconclusive": [], "literal_violations": [],
           "gcd_fail": [], "m_ne_mw": [], "divides": {"ab": 0, "bc": 0, "ca": 0, "multi": 0},
           "max_preperiod": 0}
    for a in range(1, B + 1):
        for b in range(a + 1, B + 1):
            for c in range(b + 1, B + 1):
                if c == a + b:
                    continue
                out["scanned"] += 1
                r = analyze((a, b, c), N)
                if r is None:
                    r = analyze((a, b, c), 80000)
                if r is None:
                    out["inconclusive"].append([a, b, c])
                    continue
                m = r["min_period"]
                sums = (a + b, b + c, c + a)
                divs = [s for s in sums if s % m == 0]
                if not divs:
                    out["literal_violations"].append([a, b, c, m, list(sums)])
                else:
                    # Ward gcd check: m == gcd of sums that are multiples of m
                    import math
                    gcdv = 0
                    for s in divs:
                        gcdv = math.gcd(gcdv, s)
                    if gcdv != m:
                        out["gcd_fail"].append([a, b, c, m, list(sums), gcdv])
                    key = ("ab" if sums[0] % m == 0 else "") + ("bc" if sums[1] % m == 0 else "") + ("ca" if sums[2] % m == 0 else "")
                    out["divides"]["multi" if len(divs) > 1 else key] = out["divides"].get("multi" if len(divs) > 1 else key, 0) + 1
                mw = w_min_period((a, b, c), N)
                if mw != m:
                    out["m_ne_mw"].append([a, b, c, m, mw])
                out["max_preperiod"] = max(out["max_preperiod"], r["preperiod"])
    print(json.dumps(out))
    with open(sys.argv[3] if len(sys.argv) > 3 else "/dev/stdout", "w") as f:
        json.dump(out, f)


if __name__ == "__main__":
    main()
