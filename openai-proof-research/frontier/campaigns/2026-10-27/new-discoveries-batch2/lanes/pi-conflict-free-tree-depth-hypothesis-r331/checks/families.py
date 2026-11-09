#!/usr/bin/env python3
"""Family checks v2: symbolic D_C (brooms/A_k) and D_spider validated against
the exact tree-level solver D_of; clawstars computed directly with D_of."""
import json, os, sys, math, datetime
from functools import lru_cache

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from scan_trees import enumerate_unlabeled, D_of, canon

@lru_cache(maxsize=None)
def D_P(m):
    return (m - 1).bit_length() if m >= 1 else 0

@lru_cache(maxsize=None)
def D_C(s, k):
    """D of component: center with k leaves and a stub path of s edges. n=k+s+1."""
    if s == 0:
        return k
    n = k + s + 1
    cands = {1, s}
    for a in (n // 2, (n + 1) // 2):
        if 2 <= a <= s:
            cands.add(a)
    mind = min(abs(n - 2 * a) for a in cands)
    best = None
    for a in cands:
        if abs(n - 2 * a) != mind:
            continue
        v = 1 + max(D_P(a), D_C(s - a, k))
        best = v if best is None else min(best, v)
    return best

@lru_cache(maxsize=None)
def D_spider(state):
    if not state:
        return 0
    n = 1 + sum(state)
    smax = state[-1]
    cands = {1, smax}
    for a in (n // 2, (n + 1) // 2):
        if 2 <= a <= smax:
            cands.add(a)
    mind = min(abs(n - 2 * a) for a in cands)
    best = None
    for a in cands:
        if abs(n - 2 * a) != mind:
            continue
        lst = list(state)
        lst[-1] -= a
        if lst[-1] == 0:
            lst.pop()
        v = 1 + max(D_P(a), D_spider(tuple(lst)))
        best = v if best is None else min(best, v)
    return best

def broom_tree(k, s):
    edges = [(0, i + 1) for i in range(k)]
    nxt = k + 1; prev = 0
    for j in range(s):
        edges.append((prev, nxt)); prev = nxt; nxt += 1
    return len(edges) + 1 - (0), tuple(edges)  # n, edges

def spider_tree(arms):
    edges = []; nxt = 1
    for l in arms:
        prev = 0
        for j in range(l):
            edges.append((prev, nxt)); prev = nxt; nxt += 1
    return nxt, tuple(edges)

def clawstar_tree(m, p):
    edges = []; nxt = 1
    for i in range(m):
        b = nxt; nxt += 1
        edges.append((0, b))
        for j in range(p):
            edges.append((b, nxt)); nxt += 1
    return nxt, tuple(edges)

def A_k_tree(k):
    edges = [(0, i + 1) for i in range(k - 1)]
    nxt = k; prev = 0
    for j in range(2 ** (k - 1) - 1):
        edges.append((prev, nxt)); prev = nxt; nxt += 1
    return nxt, tuple(edges)

def main():
    out = {"generated_at": datetime.datetime.now(datetime.timezone.utc).isoformat()}
    # --- validation of symbolic vs exact ---
    fams = []
    for k in range(0, 15):
        for s in range(0, 17 - max(k, 1)):
            n = k + s + 1
            if n < 2 or n > 16:
                continue
            n2, e = broom_tree(k, s)
            assert n2 == n
            fams.append((("C", s, k), n, D_C(s, k), D_of(n, e)))
    for m in range(2, 8):
        for l in range(1, 15):
            n = 1 + m * l
            if n > 16:
                continue
            n2, e = spider_tree((l,) * m)
            fams.append((("S", m, l), n, D_spider((l,) * m), D_of(n, e)))
    bad = [f for f in fams if f[2] != f[3]]
    print(f"symbolic validation: {len(fams)} pairs, {len(bad)} mismatches")
    for f in bad[:10]:
        print("MISMATCH", f)
    out["validation"] = {"pairs": len(fams), "mismatches": len(bad)}

    # --- clawstars via exact solver ---
    cw = {"all_ok": True, "min_slack": None, "pattern_viol": 0}
    for m in range(2, 81):
        for p in (1, 2, 3, 5, 8, 20, 60, 200, 700):
            n, e = clawstar_tree(m, p)
            if n > 60000:
                continue
            D = D_of(n, e)
            Delta = max(m, p + 1)
            L = (n - 1).bit_length()
            ok = D < 2 * max(Delta, L)
            sl = 2 * max(Delta, L) - D
            if cw["min_slack"] is None or sl < cw["min_slack"][0]:
                cw["min_slack"] = (sl, m, p, D, n)
            if not ok:
                cw["all_ok"] = False
                print("CLAWSTAR VIOLATION", m, p, D, n)
            if D > Delta + math.ceil(math.log2(n / Delta)):
                cw["pattern_viol"] += 1
    out["clawstars"] = cw
    print("clawstars all_ok:", cw["all_ok"], "min_slack:", cw["min_slack"],
          "pattern_viol:", cw["pattern_viol"])

    # --- A_k symbolic to k=128 ---
    a_res = []
    ok_all = True
    for k in range(2, 129):
        D = D_C(2 ** (k - 1) - 1, k - 1)
        n = k + 2 ** (k - 1)
        Delta = k
        L = (n - 1).bit_length()
        ok = D < 2 * max(Delta, L)
        ok_all &= ok
        a_res.append({"k": k, "n": n, "D": D, "2k-D": 2 * k - D, "Delta": Delta,
                      "L": L, "ok": ok})
    out["A_k"] = {"all_ok": ok_all, "data": a_res}
    print("A_k all D<2max(Delta,L)=2k:", ok_all)
    print("A_k (k, D, 2k-D) samples:", [(r["k"], r["D"], r["2k-D"]) for r in a_res[::16]])
    # A_k exact-vs-symbolic cross-check for k <= 12 (n <= 12+2048)
    mism = 0
    for k in range(2, 13):
        n, e = A_k_tree(k)
        if D_of(n, e) != D_C(2 ** (k - 1) - 1, k - 1):
            mism += 1
            print("A_k MISMATCH k=", k)
    out["A_k_crosscheck_mismatches"] = mism
    print("A_k cross-check (k<=12) mismatches:", mism)

    # --- brooms symbolic wide ---
    b_ok = True; b_worst = None; bviol = []
    for k in range(1, 65):
        for t in range(0, 240):
            l = max(1, int(2 ** (t / 8.0)))
            D = D_C(l, k)
            n = k + l + 1
            Delta = k + 1
            L = (n - 1).bit_length()
            sl = 2 * max(Delta, L) - D
            if b_worst is None or sl < b_worst[0]:
                b_worst = (sl, k, l, D, n)
            if sl <= 0:
                b_ok = False
                bviol.append((k, l, D, n))
    out["brooms"] = {"all_ok": b_ok, "min_slack": b_worst, "violations": bviol}
    print("brooms all_ok:", b_ok, "min_slack:", b_worst)

    # --- spiders symbolic wide ---
    s_ok = True; s_worst = None; sviol = []
    for m in range(2, 65):
        for t in range(0, 240):
            l = max(1, int(2 ** (t / 8.0)))
            D = D_spider((l,) * m)
            n = 1 + m * l
            Delta = m
            L = (n - 1).bit_length()
            sl = 2 * max(Delta, L) - D
            if s_worst is None or sl < s_worst[0]:
                s_worst = (sl, m, l, D, n)
            if sl <= 0:
                s_ok = False
                sviol.append((m, l, D, n))
    out["spiders"] = {"all_ok": s_ok, "min_slack": s_worst, "violations": sviol}
    print("spiders all_ok:", s_ok, "min_slack:", s_worst)

    # --- pattern D <= Delta + ceil(log2(n/Delta)) on families ---
    pv = []
    for k in range(2, 129):
        r = a_res[k - 2]
        if r["D"] > r["Delta"] + math.ceil(math.log2(r["n"] / r["Delta"])):
            pv.append(("A_k", r["k"], r["D"], r["Delta"], r["n"]))
    for k in range(1, 65):
        for t in range(0, 240, 3):
            l = max(1, int(2 ** (t / 8.0)))
            D = D_C(l, k); n = k + l + 1; Delta = k + 1
            if D > Delta + math.ceil(math.log2(n / Delta)):
                pv.append(("broom", k, l, D, Delta, n))
    for m in range(2, 65):
        for t in range(0, 240, 3):
            l = max(1, int(2 ** (t / 8.0)))
            D = D_spider((l,) * m); n = 1 + m * l; Delta = m
            if D > Delta + math.ceil(math.log2(n / Delta)):
                pv.append(("spider", m, l, D, Delta, n))
    out["pattern_violations"] = pv
    print("family pattern violations:", len(pv), pv[:5])

    W = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "work")
    os.makedirs(W, exist_ok=True)
    with open(os.path.join(W, "families.json"), "w") as f:
        json.dump(out, f, indent=1, default=str)
    print("DONE", datetime.datetime.now(datetime.timezone.utc).isoformat())

if __name__ == "__main__":
    main()
