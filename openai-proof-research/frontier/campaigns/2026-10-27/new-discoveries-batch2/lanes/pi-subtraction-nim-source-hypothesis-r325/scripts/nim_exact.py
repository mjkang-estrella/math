"""Exact minimal eventual period for 3-element subtraction Nim (MathDB 375237).

g(n) = mex{ g(n-s) : s in S, s <= n },  g(0) = mex(empty) = 0.

Rigor chain (no finite-tail guess):
  1. The trajectory g[0..n] is the true Nim sequence by induction (init
     g[0..c-1] computed by the literal mex rule, each later value uses only
     indices n+1-s >= n+1-c, all inside the last-c window).
  2. The state W(n) = (g(n-c+1..n)) evolves deterministically. A first repeat
     W(start) = W(nrep) proves the INFINITE sequence equals the cycle
     g[start..nrep-1] repeated forever (determinism).
  3. Minimal eventual period m = least p | (nrep-start) with cycle[i]=cycle[i+p].
     Minimal preperiod n0 = 1 + last index i with g[i] != g[i+m] (valid region).
"""
import sys


def analyze(S, N):
    a, b, c = S
    moves = (a, b, c)
    g = [0] * (N + 1)
    for n in range(1, min(c - 1, N) + 1):     # exact init g[1..c-1]
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
            return {"preperiod": pre, "min_period": m, "cycle_start": start,
                    "cycle_len": L, "valid_upto": n, "g": g}
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


def crosscheck(S, res, N):
    """Independent full recomputation + diagnostics. Returns failure list."""
    a, b, c = S
    g2 = [0] * (N + 1)
    for n in range(1, N + 1):
        s = set()
        for mv in (a, b, c):
            if mv <= n:
                s.add(g2[n - mv])
        i = 0
        while i in s:
            i += 1
        g2[n] = i
    fails = []
    v = res["valid_upto"]
    m = res["min_period"]
    if g2[:v + 1] != res["g"][:v + 1]:
        fails.append("trajectory mismatch on valid region")
    half = N // 2
    if any(g2[n] != g2[n + m] for n in range(half, N - m + 1)):
        fails.append(f"m={m} not periodic on independent far tail")
    for p in range(1, m):
        if not any(g2[n] != g2[n + p] for n in range(half, N - p + 1)):
            fails.append(f"smaller eventual period p={p} on far tail")
            break
    # preperiod minimality: divergence exactly at pre-1 (if pre > 0)
    pre = res["preperiod"]
    if pre > 0 and g2[pre - 1] == g2[pre - 1 + m] and pre - 1 + m <= N:
        fails.append("preperiod not minimal")
    return fails


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "scan"
    if mode == "single":
        S = tuple(int(x) for x in sys.argv[2:5])
        N = int(sys.argv[5]) if len(sys.argv) > 5 else 6000
        r = analyze(S, N)
        a, b, c = S
        if r is None:
            print(f"S={S}: no state cycle within N={N} (inconclusive)")
            return
        print(f"S={S} min_preperiod={r['preperiod']} min_period={r['min_period']} cycle_len={r['cycle_len']} start={r['cycle_start']}")
        m = r["min_period"]
        for p in (a + b, b + c, c + a):
            print(f"  candidate {p}: eventual period iff m|p -> {p % m == 0}")
        print("  crosscheck:", crosscheck(S, r, N) or "OK")
        return

    B = int(sys.argv[2]) if len(sys.argv) > 2 else 25
    N = int(sys.argv[3]) if len(sys.argv) > 3 else 3000
    lo = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    hi = int(sys.argv[5]) if len(sys.argv) > 5 else B
    out = {"scanned": 0, "inconclusive": [], "literal_violations": [],
           "minimal_reading_violations": 0, "not_dividing_ab": [], "results": []}
    for a in range(lo, hi + 1):
        for b in range(a + 1, B + 1):
            for c in range(b + 1, B + 1):
                if c == a + b:
                    continue
                out["scanned"] += 1
                r = analyze((a, b, c), N)
                if r is None:
                    r = analyze((a, b, c), 60000)
                if r is None:
                    out["inconclusive"].append([a, b, c])
                    continue
                m = r["min_period"]
                sums = (a + b, b + c, c + a)
                cc = crosscheck((a, b, c), r, 30000)
                rec = [a, b, c, m, r["preperiod"], sums.index(next(s for s in sums if s % m == 0)) if any(s % m == 0 for s in sums) else -1, cc]
                out["results"].append(rec)
                if not any(s % m == 0 for s in sums):
                    out["literal_violations"].append([a, b, c, m, sums, cc])
                if m not in sums:
                    out["minimal_reading_violations"] += 1
                if m % sums[0] != 0:
                    out["not_dividing_ab"].append([a, b, c, m, sums])
    import json
    print(json.dumps({k: (v if k != "results" else v[:5]) for k, v in out.items()
                      if k != "results"} | {"n_results": len(out["results"]),
                      "results_sample": out["results"][:5]}))
    with open(sys.argv[6] if len(sys.argv) > 6 else "/dev/stdout", "w") as f:
        json.dump(out, f)


if __name__ == "__main__":
    main()
