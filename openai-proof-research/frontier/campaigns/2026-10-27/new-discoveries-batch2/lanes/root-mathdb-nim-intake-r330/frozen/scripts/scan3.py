"""Full exact scan c<=B for the divisibility form of Ward/Moriwaki conjecture.
Exact state-cycle detection; crosscheck on a sample only (runtime).
Usage: scan3.py B N out.json [crosscheck_fraction]
"""
import sys, json, random


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


def crosscheck(S, res, N=20000):
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
    v = res["valid_upto"]; m = res["min_period"]
    if g2[:v + 1] != res["g"][:v + 1]:
        return ["trajectory mismatch"]
    half = N // 2
    if any(g2[n] != g2[n + m] for n in range(half, N - m + 1)):
        return [f"m={m} not periodic on independent tail"]
    for p in range(1, m):
        if not any(g2[n] != g2[n + p] for n in range(half, N - p + 1)):
            return [f"smaller period p={p}"]
    return []


def main():
    B = int(sys.argv[1]); N = int(sys.argv[2]); out = sys.argv[3]
    frac = float(sys.argv[4]) if len(sys.argv) > 4 else 0.05
    rng = random.Random(20261031)
    res = {"scanned": 0, "inconclusive": [], "literal_violations": [],
           "crosscheck_fail": [], "max_preperiod": 0, "max_m": 0,
           "n_crosschecked": 0, "sample_results": []}
    for a in range(1, B + 1):
        for b in range(a + 1, B + 1):
            for c in range(b + 1, B + 1):
                if c == a + b:
                    continue
                res["scanned"] += 1
                r = analyze((a, b, c), N)
                if r is None:
                    r = analyze((a, b, c), 200000)
                if r is None:
                    res["inconclusive"].append([a, b, c])
                    continue
                m = r["min_period"]
                sums = (a + b, b + c, c + a)
                res["max_preperiod"] = max(res["max_preperiod"], r["preperiod"])
                res["max_m"] = max(res["max_m"], m)
                if not any(s % m == 0 for s in sums):
                    cc = crosscheck((a, b, c), r)
                    res["literal_violations"].append(
                        {"S": [a, b, c], "m": m, "sums": list(sums),
                         "cycle": r["cycle"], "preperiod": r["preperiod"],
                         "crosscheck": cc})
                elif rng.random() < frac:
                    cc = crosscheck((a, b, c), r)
                    res["n_crosschecked"] += 1
                    if cc:
                        res["crosscheck_fail"].append([a, b, c, m, cc])
    print(json.dumps({k: (v if k != "literal_violations" else v[:3])
                      for k, v in res.items()}))
    with open(out, "w") as f:
        json.dump(res, f)


if __name__ == "__main__":
    main()
