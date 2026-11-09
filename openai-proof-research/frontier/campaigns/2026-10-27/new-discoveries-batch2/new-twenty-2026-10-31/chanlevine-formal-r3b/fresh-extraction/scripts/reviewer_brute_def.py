"""Tier-1 brute force of r(C_{n,m,i}) straight from the source's DEFINITIONS (independent of lane r127).

Source: Chan-Levine, Abelian networks IV, arXiv:1804.03322v2.
  * Example 3.11 (sinkless rotor network): processing a chip at v first advances the rotor
    q(v) to the next out-edge (on C_n: flips it), THEN moves the chip along the NEW rotor.
  * Definition 4.5-4.7: trajectory digraph; legal relation x.q ->_<- x'.q' iff they have a common
    legal descendant; a component is an equivalence class of that relation.
  * Definition 5.2: x.q is recurrent iff (i) some nonempty legal execution exists and
    (ii) every x'.q' legally related to x.q legally reaches x.q.
  * Section 8.3: wt(x.q) = sum_k k*x(v_k) + #{k : q(v_k) = (v_k, v_{k-1})}  (mod n);
    r(C) = number of recurrent configurations in the component C.

Exact method.  Fix n, m and a lower bound L <= 0 on chip entries.  U = {x.q : x >= L, sum x = m} is
closed under legal moves (an entry only decreases when it is >= 1, so stays >= 0 > L-1) and is finite.
In a finite forward-closed digraph where every state has a legal move (m >= 1 forces a positive
entry), Definition 5.2 is equivalent to "x.q lies in a TERMINAL strongly connected component":
  - if x.q is in a terminal SCC T, any common descendant y lies in T and y reaches x.q, so (ii) holds;
  - otherwise x.q reaches some terminal SCC T' not containing it; any x' in T' is legally related to
    x.q (common descendant x' itself) but cannot reach x.q, so (ii) fails.
Two recurrent configurations are legally related iff they are in the same terminal SCC (a common
descendant lies in both).  Hence the recurrent components of level m correspond to terminal SCCs, and
r(C) = |T|.  We also report non-terminal nontrivial SCCs (there should be none, by Lemma 5.3(ii)).

Usage: python3 -I brute_def.py OUT.json L n:m1-m2 [n:m1-m2 ...]
"""
import json
import sys
import time


def compositions(n, m, L):
    """All tuples of length n, entries >= L, summing to m."""
    out = []
    shift = m - n * L  # substitute y = x - L >= 0, sum y = shift
    if shift < 0:
        return out
    def rec(prefix, k, rem):
        if k == n - 1:
            out.append(tuple(prefix + [rem + L]))
            return
        for a in range(rem + 1):
            prefix.append(a + L)
            rec(prefix, k + 1, rem - a)
            prefix.pop()
    rec([], 0, shift)
    return out


def analyse(n, m, L):
    xs = compositions(n, m, L)
    xidx = {x: i for i, x in enumerate(xs)}
    Q = 1 << n
    N = len(xs) * Q
    # successor function: state s = xi*Q + qm ; bit k of qm = 1 means q(v_k) = (v_k, v_{k+1}) ("+")
    def succ(s):
        xi, qm = divmod(s, Q)
        x = xs[xi]
        res = []
        for k in range(n):
            if x[k] >= 1:
                nq = qm ^ (1 << k)               # advance rotor first (flip)
                if (nq >> k) & 1:
                    t = (k + 1) % n              # new rotor points to v_{k+1}
                else:
                    t = (k - 1) % n              # new rotor points to v_{k-1}
                y = list(x)
                y[k] -= 1
                y[t] += 1
                res.append(xidx[tuple(y)] * Q + nq)
        return res

    # iterative Tarjan
    index = [-1] * N
    low = [0] * N
    onstk = bytearray(N)
    comp = [-1] * N
    stk = []
    counter = 0
    ncomp = 0
    comp_members = []
    for root in range(N):
        if index[root] != -1:
            continue
        work = [(root, succ(root), 0)]
        index[root] = low[root] = counter
        counter += 1
        stk.append(root)
        onstk[root] = 1
        while work:
            v, sv, pos = work[-1]
            if pos < len(sv):
                w = sv[pos]
                work[-1] = (v, sv, pos + 1)
                if index[w] == -1:
                    index[w] = low[w] = counter
                    counter += 1
                    stk.append(w)
                    onstk[w] = 1
                    work.append((w, succ(w), 0))
                elif onstk[w]:
                    if index[w] < low[v]:
                        low[v] = index[w]
            else:
                work.pop()
                if work:
                    u = work[-1][0]
                    if low[v] < low[u]:
                        low[u] = low[v]
                if low[v] == index[v]:
                    members = []
                    while True:
                        w = stk.pop()
                        onstk[w] = 0
                        comp[w] = ncomp
                        members.append(w)
                        if w == v:
                            break
                    comp_members.append(members)
                    ncomp += 1
    del index, low, onstk

    def weight(s):
        xi, qm = divmod(s, Q)
        x = xs[xi]
        w = sum(k * x[k] for k in range(n))
        w += sum(1 for k in range(n) if not (qm >> k) & 1)
        return w % n

    terminal = []
    nontriv_nonterminal = 0
    for c, members in enumerate(comp_members):
        is_term = True
        for s in members:
            for t in succ(s):
                if comp[t] != c:
                    is_term = False
                    break
            if not is_term:
                break
        nontrivial = len(members) > 1  # no self-loops exist: a chip always moves to a neighbour
        if is_term:
            ws = sorted({weight(s) for s in members})
            minx = min(min(xs[s // Q]) for s in members)
            terminal.append({"size": len(members), "weights": ws, "min_entry": minx})
        elif nontrivial:
            nontriv_nonterminal += 1
    by_w = {}
    for T in terminal:
        if len(T["weights"]) == 1:
            by_w.setdefault(T["weights"][0], []).append(T["size"])
    unique = (len(terminal) == n and all(len(T["weights"]) == 1 for T in terminal)
              and sorted(by_w) == list(range(n)) and all(len(v) == 1 for v in by_w.values()))
    r = [by_w[i][0] if (i in by_w and len(by_w[i]) == 1) else None for i in range(n)]
    return {
        "n": n, "m": m, "L": L, "states": N, "sccs": ncomp,
        "terminal_sccs": len(terminal),
        "terminal_all_constant_weight": all(len(T["weights"]) == 1 for T in terminal),
        "terminal_min_entry": min(T["min_entry"] for T in terminal) if terminal else None,
        "nontrivial_nonterminal_sccs": nontriv_nonterminal,
        "unique_component_per_weight": unique,
        "r": r,
        "total_recurrent": sum(T["size"] for T in terminal),
    }


def main():
    out = sys.argv[1]
    L = int(sys.argv[2])
    jobs = []
    for spec in sys.argv[3:]:
        a, b = spec.split(":")
        m1, m2 = b.split("-")
        for m in range(int(m1), int(m2) + 1):
            jobs.append((int(a), m))
    results = []
    for n, m in jobs:
        t0 = time.process_time()
        res = analyse(n, m, L)
        res["cpu_s"] = round(time.process_time() - t0, 3)
        results.append(res)
        print(json.dumps(res), flush=True)
    with open(out, "w") as f:
        json.dump(results, f, indent=1)


if __name__ == "__main__":
    main()
