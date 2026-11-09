"""W021 toy exact-algebra certificate (see certificate-preregistration.md).

Checks the block identity, post-construction digit relabelling, shifts, tails,
signed/wide exponents and composite/repeated-point values against direct
products. Plain Horner evaluation; NOT a Kedlaya--Umans implementation.
Stdlib only. Run once: python3 -I certificate.py OUT_JSON
"""
import json
import sys
import time

CAP = 20000
DEADLINE = 60.0
T0 = time.monotonic()


class Budget(Exception):
    pass


class Meter:
    def __init__(self):
        self.cand = 0
        self.ref = 0

    def charge(self, which, k=1):
        if which == "cand":
            self.cand += k
        else:
            self.ref += k
        if self.cand + self.ref > CAP:
            raise Budget("event cap exceeded")
        if time.monotonic() - T0 > DEADLINE:
            raise Budget("deadline exceeded")


M = Meter()


def mul(a, b, n):
    M.charge("cand")
    return a * b % n


def sub(a, b, n):
    M.charge("cand")
    return (a - b) % n


def powmod(base, e, n, inv_base):
    """Binary powering with charged multiplications; negative e uses inv_base."""
    if e < 0:
        base, e = inv_base, -e
    result, sq = 1, base % n
    while e:
        if e & 1:
            result = mul(result, sq, n)
        e >>= 1
        if e:
            sq = mul(sq, sq, n)
    return result


def bimul(P, Q, n):
    """Dense bivariate product; P[h][e] coefficient of X^e Y^h. Charged per dense slot pair."""
    hp, ep = len(P), len(P[0])
    hq, eq = len(Q), len(Q[0])
    R = [[0] * (ep + eq - 1) for _ in range(hp + hq - 1)]
    for h1 in range(hp):
        for e1 in range(ep):
            a = P[h1][e1]
            for h2 in range(hq):
                for e2 in range(eq):
                    R[h1 + h2][e1 + e2] = (R[h1 + h2][e1 + e2] + mul(a, Q[h2][e2], n)) % n
    return R


def build_F(cs, n):
    level = []
    for j, c in enumerate(cs):
        P = [[0] * (j + 1), [0] * (j + 1)]
        P[0][0] = 1
        P[1][j] = (-c) % n
        level.append(P)
    slots = []
    while len(level) > 1:
        nxt = []
        for t in range(0, len(level) - 1, 2):
            nxt.append(bimul(level[t], level[t + 1], n))
        if len(level) % 2:
            nxt.append(level[-1])
        level = nxt
        slots.append(sum(len(P) * len(P[0]) for P in level))
    return level[0], slots


def degrees(P):
    dy = max((h for h in range(len(P)) if any(P[h])), default=0)
    dx = max((e for row in P for e in range(len(row)) if row[e]), default=0)
    return dx, dy


def relabel(F, b):
    G = {}
    for h, row in enumerate(F):
        for e, c in enumerate(row):
            if c:
                G[(e % b, e // b, h)] = c
    return G


def eval_tri(G, x0, x1, y, n):
    total = 0
    for (e0, e1, h), c in G.items():  # monomial-wise; toy evaluator only
        t = c
        for _ in range(e0):
            t = mul(t, x0, n)
        for _ in range(e1):
            t = mul(t, x1, n)
        for _ in range(h):
            t = mul(t, y, n)
        total = (total + t) % n
    return total


def eval_bi(F, x, y, n):
    acc = 0
    for h in reversed(range(len(F))):
        row = F[h]
        v = 0
        for e in reversed(range(len(row))):
            v = (mul(v, x, n) + row[e]) % n
        acc = (mul(acc, y, n) + v) % n
    return acc


def candidate(n, alpha, A, D, C, L, b):
    inv = pow(alpha, -1, n)
    M.charge("cand")
    p = lambda e: powmod(alpha, e, n, inv)
    r0 = p(A + D)
    s2A = p(2 * A)
    g = p(2 * A * b)
    hstep = p(2 * A * b * b)
    s0 = p(A * b * b + D * b)
    y0 = p(C)
    cs, c, r = [], 1, r0
    for j in range(b):
        cs.append(c)
        c = mul(c, r, n)
        r = mul(r, s2A, n)
    F, slots = build_F(cs, n)
    dx, dy = degrees(F)
    G = relabel(F, b)
    gdeg = tuple(max((k[i] for k in G), default=0) for i in range(3))
    K = L // b
    X, Xb, Y, s = 1, 1, y0, s0
    blocks = []
    total = 1
    for k in range(K):
        vg = eval_tri(G, X, Xb, Y, n)
        vf = eval_bi(F, X, Y, n)
        blocks.append({"k": k, "G": vg, "F": vf, "points": [X, Xb, Y]})
        total = mul(total, vg, n)
        X = mul(X, g, n)
        Xb = mul(Xb, hstep, n)
        Y = mul(Y, s, n)
        s = mul(s, hstep, n)
    # tail: alpha^f(bK) = Y_K; ratio alpha^(A(2bK+1)+D) = r0 * X_K
    v, rr = Y, mul(r0, X, n)
    tail = []
    for _ in range(L - b * K):
        leaf = sub(1, v, n)
        tail.append(leaf)
        total = mul(total, leaf, n)
        v = mul(v, rr, n)
        rr = mul(rr, s2A, n)
    # negative control N1: psi applied to factors before multiplication
    pre = {(0, 0, 0): 1}
    for j, cj in enumerate(cs):
        fac = {(0, 0, 0): 1, (j % b, j // b, 1): (-cj) % n}
        out = {}
        for k1, a1 in pre.items():
            for k2, a2 in fac.items():
                key = (k1[0] + k2[0], k1[1] + k2[1], k1[2] + k2[2])
                out[key] = (out.get(key, 0) + a1 * a2) % n
        pre = {k_: v_ for k_, v_ in out.items() if v_}
    pre_x0 = max((k_[0] for k_ in pre), default=0)
    pre_eval = [eval_tri(pre, bl["points"][0], bl["points"][1], bl["points"][2], n) for bl in blocks]
    return {
        "total": total, "blocks": blocks, "tail": tail, "degX": dx, "degY": dy,
        "relabel_degrees": list(gdeg), "level_slots": slots, "K": K,
        "N1_pre_relabel_maxX0": pre_x0, "N1_equal_as_polys": pre == G,
        "N1_eval_matches_F": [pv == bl["F"] for pv, bl in zip(pre_eval, blocks)],
    }


def f(A, D, C, i):
    return A * i * i + D * i + C


def direct(n, alpha, A, D, C, idxs):
    tot, leaves = 1, []
    for i in idxs:
        M.charge("ref", 2)
        leaf = (1 - pow(alpha, f(A, D, C, i), n)) % n
        leaves.append(leaf)
        tot = tot * leaf % n
    return tot, leaves


CASES = [
    ("K1", 15, 2, 1, 0, 0, 7, 2, None),
    ("K2", 91, 3, 5, -7, -11, 23, 3, None),
    ("K3", 1001, 10, -3, 4, 2**70 + 5, 20, 4, None),
    ("K4", 45, 2, 6, 12, 0, 17, 3, None),
    ("K5", 221, 220, 1, 1, 1, 12, 3, None),
    ("K6", 1155, 2, -(2**64 + 3), 2**40, -(2**90), 10, 2, None),
    ("K7", 35, 3, 2, 1, 0, 2, 3, None),
    ("S1", 91, 3, 5, -7, -11, 11, 3, 9),
]


def run_case(cid, n, alpha, A, D, C, L, b, a):
    c0, r0 = M.cand, M.ref
    if a is None:
        cand = candidate(n, alpha, A, D, C, L, b)
        dtot, leaves = direct(n, alpha, A, D, C, range(L))
        base = 0
    else:
        cand = candidate(n, alpha, A, D + 2 * A * a, C + D * a + A * a * a, L, b)
        dtot, leaves = direct(n, alpha, A, D, C, range(a, a + L))
        base = 0
    c1 = []
    for bl in cand["blocks"]:
        k = bl["k"]
        dp = 1
        for leaf in leaves[base + b * k: base + b * k + b]:
            dp = dp * leaf % n
        c1.append(bl["G"] == bl["F"] == dp)
    K = cand["K"]
    c1_tail = cand["tail"] == leaves[b * K:]
    c3 = (cand["degX"] <= b * (b - 1) // 2 and cand["degY"] <= b
          and cand["relabel_degrees"][0] <= b - 1
          and cand["relabel_degrees"][1] <= (b - 1) // 2
          and cand["relabel_degrees"][2] <= b)
    res = {
        "id": cid, "N": n, "alpha": alpha, "A": str(A), "D": str(D), "C": str(C), "L": L, "b": b,
        "shift_a": a, "candidate_total": cand["total"], "direct_total": dtot,
        "C1_blocks": c1, "C1_tail": c1_tail, "C2_total": cand["total"] == dtot,
        "C3_degrees": c3, "degX": cand["degX"], "degY": cand["degY"],
        "relabel_degrees": cand["relabel_degrees"], "level_slots": cand["level_slots"],
        "zero_leaves": sum(1 for x in leaves if x == 0),
        "distinct_points": len({tuple(bl["points"]) for bl in cand["blocks"]}),
        "blocks": len(cand["blocks"]),
        "N1_pre_relabel_maxX0": cand["N1_pre_relabel_maxX0"],
        "N1_equal_as_polys": cand["N1_equal_as_polys"],
        "N1_eval_matches_F": cand["N1_eval_matches_F"],
        "events_candidate": M.cand - c0, "events_reference": M.ref - r0,
    }
    if a is not None:
        res["C4_shift"] = cand["total"] == dtot
    return res


def main(out):
    results, failures = [], []
    for case in CASES:
        try:
            r = run_case(*case)
        except Exception as exc:  # retained as failure
            r = {"id": case[0], "error": repr(exc)}
            failures.append(case[0])
            results.append(r)
            print(case[0], "ERROR", repr(exc))
            if isinstance(exc, Budget):
                break
            continue
        ok = (all(r["C1_blocks"]) and r["C1_tail"] and r["C2_total"] and r["C3_degrees"]
              and r.get("C4_shift", True))
        r["pass"] = ok
        if not ok:
            failures.append(r["id"])
        results.append(r)
        print(r["id"], "pass" if ok else "FAIL", "cand_events", r["events_candidate"],
              "ref_events", r["events_reference"], "degX/degY", r["degX"], r["degY"],
              "relabel", r["relabel_degrees"], "zeros", r["zero_leaves"],
              "blocks/distinct_pts", r["blocks"], r["distinct_points"],
              "N1_maxX0", r["N1_pre_relabel_maxX0"], "N1_polys_equal", r["N1_equal_as_polys"])
    elapsed = time.monotonic() - T0
    summary = {"cases": len(CASES), "failures": failures, "events_candidate": M.cand,
               "events_reference": M.ref, "events_total": M.cand + M.ref, "cap": CAP,
               "elapsed_s": elapsed, "deadline_s": DEADLINE,
               "within_budget": M.cand + M.ref <= CAP and elapsed <= DEADLINE,
               "python": sys.version}
    print("SUMMARY", json.dumps(summary))
    with open(out, "w") as fh:
        json.dump({"summary": summary, "results": results}, fh, indent=2)


if __name__ == "__main__":
    main(sys.argv[1])
