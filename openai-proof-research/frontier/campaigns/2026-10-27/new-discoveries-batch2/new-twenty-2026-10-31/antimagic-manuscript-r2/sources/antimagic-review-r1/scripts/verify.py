"""Independent re-implementation (review lane antimagic-review-r1).

Written from the definitions (source Defs 1.1-1.4) and the TEXT of
expanded-corpus-r142/outputs/antimagic/proof.md only. It does not import or
read the discovery lane's scripts.

Tree model: vertex (h, i), 0 <= h <= n, 0 <= i < t**h; the children of (h, i)
are (h+1, t*i + j), 0 <= j < t. Every edge is identified with its lower
endpoint (h, i), h >= 1, and E_h is the set of t**h edges into row h.
A labelling is lab[h][i] for h = 1..n.

Usage: python3 -I verify.py MODE [args]
  MODE grid  T_MAX EDGE_CAP   : verify every even t <= T_MAX, every n >= 1 with m <= EDGE_CAP
  MODE one   t n              : verify one case
  MODE neg   t n              : negative controls (checker sensitivity)
  MODE ident T_MAX N_MAX      : integer identities of the proof (no tree built)
  MODE brute                  : exhaustive minimum over all labellings for tiny trees
Output: JSON lines on stdout.
"""
import itertools
import json
import resource
import sys
import time


# ------------------------------------------------------------------ checker
def check(t, n, lab):
    """Return a dict: bijective onto [1, m], proper on every edge, #colours."""
    m = sum(t ** h for h in range(1, n + 1))
    # shape
    for h in range(1, n + 1):
        if len(lab[h]) != t ** h:
            return {"ok": False, "why": "shape row %d" % h}
    flat = [x for h in range(1, n + 1) for x in lab[h]]
    if len(flat) != m:
        return {"ok": False, "why": "edge count"}
    seen = bytearray(m + 1)
    for x in flat:
        if not (isinstance(x, int) and 1 <= x <= m) or seen[x]:
            return {"ok": False, "why": "not a bijection onto [1,m] at %r" % (x,)}
        seen[x] = 1
    # weights, computed from the incidence definition
    w = [None] * (n + 1)
    for h in range(0, n + 1):
        row = [0] * (t ** h)
        if h >= 1:
            up = lab[h]
            for i in range(t ** h):
                row[i] += up[i]
        if h < n:
            down = lab[h + 1]
            for i in range(t ** h):
                base = t * i
                s = 0
                for j in range(t):
                    s += down[base + j]
                row[i] += s
        w[h] = row
    # properness on every edge (h-1, i // t) -- (h, i)
    for h in range(1, n + 1):
        wu, wv = w[h - 1], w[h]
        for i in range(t ** h):
            if wu[i // t] == wv[i]:
                return {"ok": False, "why": "improper edge into (%d,%d), colour %d" % (h, i, wv[i])}
    colours = set()
    for h in range(n + 1):
        colours.update(w[h])
    leaves = t ** n
    return {"ok": len(colours) == leaves + 1, "m": m, "colours": len(colours),
            "l_plus_1": leaves + 1,
            "why": "" if len(colours) == leaves + 1 else "colour count %d" % len(colours)}


# ------------------------------------------------------------- construction
def build(t, n, t2_swap=True, keep_root_order=True):
    assert t >= 2 and t % 2 == 0 and n >= 1
    m = sum(t ** h for h in range(1, n + 1))
    lab = [None] + [[0] * (t ** h) for h in range(1, n + 1)]
    if n == 1:                                   # proof.md 2.1
        lab[1] = list(range(1, t + 1))
        return lab
    if n == 2 and t == 2:                        # proof.md 2.2
        lab[1] = [1, 4]
        lab[2] = [2, 3, 6, 5]
        return lab
    if n == 2:                                   # proof.md 2.3
        s = t // 2
        M = t + t * t
        rho = [3 * s + 2 - i for i in range(1, t)]          # x_1 .. x_{t-1}
        Sstar = [1] + list(range(3, s + 3)) + list(range(3 * s + 2, 4 * s + 1))
        B = list(range(2 * t + 1, M + 1))
        npr = t - 1
        kappa = (npr - 1) // 2
        blocks = [B[b * npr:(b + 1) * npr] for b in range(t)]   # blocks 1..t
        tuples = [[] for _ in range(npr)]
        for b in range(1, s):                     # outer pairs, b <= s-1
            lo, hi = blocks[b - 1], blocks[t - b]
            for j in range(npr):
                tuples[j] += [lo[j], hi[npr - 1 - j]]
        beta = blocks[s - 1][0] - 1               # middle run [beta+1, beta+4kappa+2]
        run = blocks[s - 1] + blocks[s]
        assert run == list(range(beta + 1, beta + 4 * kappa + 3))
        mids = [(beta + 2 * i + 1, beta + 3 * kappa + 2 - i) for i in range(0, kappa + 1)]
        mids += [(beta + 2 * i, beta + 4 * kappa + 3 - i) for i in range(1, kappa + 1)]
        assert sorted(x for p in mids for x in p) == run
        for j in range(npr):
            tuples[j] += list(mids[j])
        sums = [sum(tp) for tp in tuples]
        order = sorted(range(npr), key=lambda j: sums[j])
        Gamma = sums[order[0]] - 1
        assert [sums[j] for j in order] == list(range(Gamma + 1, Gamma + npr + 1))
        # x* is child 0, x_i is child i
        lab[1] = [2] + rho
        lab[2][0:t] = Sstar
        for i in range(1, t):
            tp = tuples[order[i - 1]]             # sum Gamma + i
            lab[2][t * i:t * i + t] = tp
        return lab
    # ---------------------------------------------------------------- n >= 3
    N = sum(t ** h for h in range(1, n))
    q = t ** (n - 1)
    k = q // 2
    assert (N - t) % 2 == 0
    R = (N - t) // 2
    Z = R + 1
    assert m == N + t * q
    # D ranges: D_{n-1} = [1,k], then D_{n-2}, ..., D_2
    D = {}
    start = 1
    for h in range(n - 1, 1, -1):
        size = t ** h // 2
        D[h] = list(range(start, start + size))
        start += size
    assert start - 1 == R
    A1 = [Z] + list(range(N - t + 2, N + 1))
    lab[1] = list(A1)                             # x_Z is child 0, x_N child t-1
    half = t // 2
    for h in range(1, n - 1):                     # children of V_h, edges E_{h+1}
        Dh = D[h + 1]
        assert len(Dh) == (t ** h) * half
        for i in range(t ** h):
            grp = Dh[i * half:(i + 1) * half]
            labels = []
            for d in grp:
                labels += [Z - d, Z + d]
            lab[h + 1][t * i:t * i + t] = labels
    if t == 2 and t2_swap:                        # proof.md 2.4(g)
        assert lab[1] == [Z, N] and set(D[2]) == {R - 1, R}
        lab[2][0:2] = [Z - R + 1, Z + R]          # children of x_Z
        lab[2][2:4] = [Z - R, Z + R - 1]          # children of x_N
    # leaf tuples
    def sigma(a):
        return 2 * a if a <= k else 2 * (a - k) - 1
    def lam(b, a):
        return N + (b - 1) * q + a
    def T(a):
        out = []
        for b in range(1, half):
            out += [lam(b, a), lam(t + 1 - b, q + 1 - a)]
        out += [lam(half, a), lam(half + 1, q + 1 - sigma(a))]
        return out
    used = bytearray(q + 1)
    for i in range(q):
        eps = lab[n - 1][i] - Z
        assert eps != 0 and abs(eps) <= k
        a = eps if eps > 0 else k + (k + 1 + eps)  # delta(a) = -eps
        assert a - sigma(a) == -eps
        assert not used[a]
        used[a] = 1
        lab[n][t * i:t * i + t] = T(a)
    return lab


# ------------------------------------------------- second, edge-list checker
def check_edgelist(t, n, lab):
    """Independent second checker: explicit vertex ids and edge list."""
    vid = {}
    for h in range(n + 1):
        for i in range(t ** h):
            vid[(h, i)] = len(vid)
    edges = []
    for h in range(1, n + 1):
        for i in range(t ** h):
            edges.append((vid[(h - 1, i // t)], vid[(h, i)], lab[h][i]))
    m = len(edges)
    labels = sorted(e[2] for e in edges)
    if labels != list(range(1, m + 1)):
        return {"ok": False, "why": "not bijective"}
    deg = [0] * len(vid); w = [0] * len(vid)
    for u, v, x in edges:
        w[u] += x; w[v] += x; deg[u] += 1; deg[v] += 1
    if any(w[u] == w[v] for u, v, _ in edges):
        return {"ok": False, "why": "improper"}
    leaves = sum(1 for d in deg if d == 1)
    assert leaves == t ** n
    c = len(set(w))
    return {"ok": c == leaves + 1, "colours": c, "l_plus_1": leaves + 1}


def leaf_pair_swap(t, n, lab):
    """Swap one leaf label between the first two parents in V_{n-1}."""
    lab2 = [None] + [list(r) for r in lab[1:]]
    lab2[n][0], lab2[n][t] = lab2[n][t], lab2[n][0]
    return lab2


# ------------------------------- closed form proposed for the Lean route (gate C)
def closed_label(t, n, h, i):
    """Label of the edge into vertex (h, i), n >= 3, by piecewise-affine formulas.
    Internal rows 2..n-1: r = offset(h) + i, d = 1 + r // 2, label = Z - d (r even) or Z + d (r odd),
    offset(h) = t^(h+1) + ... + t^(n-1). Row 1: [Z, N-t+2, ..., N]. t = 2: transpose row-2 indices 1, 3.
    Leaves: parent label Z + eps; a = eps (eps > 0) or q + 1 + eps (eps < 0);
    slot j: 2(b-1) -> lam_b(a); 2(b-1)+1 -> lam_{t+1-b}(q+1-a) (b < t/2);
    t-2 -> lam_{t/2}(a); t-1 -> lam_{t/2+1}(q+1-sigma(a))."""
    N = sum(t ** g for g in range(1, n)); q = t ** (n - 1); k = q // 2; Z = (N - t) // 2 + 1
    if h == 1:
        return Z if i == 0 else N - t + 1 + i
    if h < n:
        if t == 2 and h == 2 and i in (1, 3):
            i = 4 - i
        r = sum(t ** g for g in range(h + 1, n)) + i
        d = 1 + r // 2
        return Z - d if r % 2 == 0 else Z + d
    pl = closed_label(t, n, n - 1, i // t)
    eps = pl - Z
    a = eps if eps > 0 else q + 1 + eps
    sig = 2 * a if a <= k else 2 * (a - k) - 1
    j = i % t; half = t // 2
    lam = lambda b, x: N + (b - 1) * q + x
    if j < t - 2:
        b = j // 2 + 1
        return lam(b, a) if j % 2 == 0 else lam(t + 1 - b, q + 1 - a)
    return lam(half, a) if j == t - 2 else lam(half + 1, q + 1 - sig)


# ------------------------------------------------------------ identities
def identities(tmax, nmax):
    bad = []
    cnt = 0
    for t in range(2, tmax + 1, 2):
        for n in range(3, nmax + 1):
            N = sum(t ** h for h in range(1, n)); q = t ** (n - 1); m = N + t * q
            Z = (N - t) // 2 + 1
            Gamma = (t // 2) * (2 * N + t * q + 1)
            root = Z + sum(range(N - t + 2, N + 1))
            conds = {
                "N-t even": (N - t) % 2 == 0,
                "root formula": root == Z + (t - 1) * N - (t - 1) * (t - 2) // 2,
                "tZ>=N": t * Z >= N,
                "Z<=q": Z <= q,
                "root in Lambda": N + 1 <= root <= m,
                "root-tZ=(t-1)N/2": 2 * (root - t * Z) == (t - 1) * N,
                "c>m": Gamma + Z > m,
                "t>=4 root not in tZ+A1": t == 2 or (t - 1) * N // 2 > N,
            }
            cnt += 1
            for kname, v in conds.items():
                if not v:
                    bad.append((t, n, kname))
    return {"mode": "ident", "cases": cnt, "failures": bad[:20], "ok": not bad}


def brute():
    """Exhaustive minimum number of colours for T(2,2) (6 edges) and T(4,1)."""
    out = []
    for (t, n) in [(2, 1), (4, 1), (2, 2)]:
        m = sum(t ** h for h in range(1, n + 1))
        best = None
        for perm in itertools.permutations(range(1, m + 1)):
            lab = [None]
            pos = 0
            for h in range(1, n + 1):
                lab.append(list(perm[pos:pos + t ** h])); pos += t ** h
            r = check(t, n, lab)
            if "colours" in r:                     # proper (local antimagic) labelling
                c = r["colours"]
                best = c if best is None else min(best, c)
        out.append({"t": t, "n": n, "min_colours": best, "l_plus_1": t ** n + 1})
    return out


def rss_mb():
    return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024.0


def main():
    mode = sys.argv[1]
    t0 = time.time()
    if mode == "one":
        t, n = int(sys.argv[2]), int(sys.argv[3])
        r = check(t, n, build(t, n)); r.update(t=t, n=n)
        print(json.dumps(r))
    elif mode == "grid":
        tmax, cap = int(sys.argv[2]), int(sys.argv[3])
        allok = True; ncase = 0
        for t in range(2, tmax + 1, 2):
            n = 1
            while True:
                m = sum(t ** h for h in range(1, n + 1))
                if m > cap:
                    break
                r = check(t, n, build(t, n)); r.update(t=t, n=n, sec=round(time.time() - t0, 2))
                print(json.dumps(r), flush=True)
                allok &= r["ok"]; ncase += 1
                n += 1
        print(json.dumps({"mode": "grid", "cases": ncase, "all_ok": allok,
                          "peak_rss_mb": round(rss_mb(), 1), "sec": round(time.time() - t0, 2)}))
    elif mode == "neg":
        t, n = int(sys.argv[2]), int(sys.argv[3])
        res = {}
        if t == 2 and n >= 3:
            res["no_t2_swap"] = check(t, n, build(t, n, t2_swap=False))
        lab = build(t, n)
        lab2 = [None] + [list(r) for r in lab[1:]]
        lab2[n][0], lab2[n - 1][0] = lab2[n - 1][0], lab2[n][0]   # swap a leaf label and an internal label
        res["swap_leaf_internal"] = check(t, n, lab2)
        lab3 = [None] + [list(r) for r in lab[1:]]
        lab3[1][0] = lab3[1][1]                                     # duplicate label
        res["duplicate"] = check(t, n, lab3)
        res["swap_leaf_internal_edgelist"] = check_edgelist(t, n, lab2)
        lab4 = leaf_pair_swap(t, n, lab)
        res["leaf_pair_swap"] = check(t, n, lab4)
        res["leaf_pair_swap_edgelist"] = check_edgelist(t, n, lab4)
        print(json.dumps({"mode": "neg", "t": t, "n": n, "results": res}))
    elif mode == "cross":
        tmax, cap = int(sys.argv[2]), int(sys.argv[3])
        allok = True; ncase = 0
        for t in range(2, tmax + 1, 2):
            n = 1
            while sum(t ** h for h in range(1, n + 1)) <= cap:
                lab = build(t, n)
                a, b = check(t, n, lab), check_edgelist(t, n, lab)
                agree = (a["ok"] == b["ok"]) and a.get("colours") == b.get("colours")
                print(json.dumps({"t": t, "n": n, "ok": a["ok"] and b["ok"] and agree}), flush=True)
                allok &= a["ok"] and b["ok"] and agree; ncase += 1
                n += 1
        print(json.dumps({"mode": "cross", "cases": ncase, "all_ok": allok, "peak_rss_mb": round(rss_mb(), 1)}))
    elif mode == "closed":
        tmax, cap = int(sys.argv[2]), int(sys.argv[3])
        allsame = True; allok = True; ncase = 0
        for t in range(2, tmax + 1, 2):
            n = 3
            while sum(t ** h for h in range(1, n + 1)) <= cap:
                lab = build(t, n)
                labc = [None] + [[closed_label(t, n, h, i) for i in range(t ** h)] for h in range(1, n + 1)]
                same = lab == labc
                r = check(t, n, labc)
                print(json.dumps({"t": t, "n": n, "same_as_build": same, "ok": r["ok"]}), flush=True)
                allsame &= same; allok &= r["ok"]; ncase += 1
                n += 1
        print(json.dumps({"mode": "closed", "cases": ncase, "all_same": allsame, "all_ok": allok,
                          "peak_rss_mb": round(rss_mb(), 1)}))
    elif mode == "ident":
        print(json.dumps(identities(int(sys.argv[2]), int(sys.argv[3]))))
    elif mode == "brute":
        print(json.dumps({"mode": "brute", "results": brute(), "sec": round(time.time() - t0, 2)}))
    print(json.dumps({"peak_rss_mb": round(rss_mb(), 1), "sec": round(time.time() - t0, 2)}), file=sys.stderr)


if __name__ == "__main__":
    main()
