#!/usr/bin/env python3
"""Bounded numerical sanity check of the algebra in proof.md (not a proof, not a gate).

For small random graphs it approximates a maximizer w of F_G by projected gradient ascent
from several starts, then checks the exact identities and inequalities used in the proof:
  * stationarity log(1/w_v) = w(N(v)) (approximately);
  * the weighted average of c_v - C(1 + log 1/w_v) is <= 0 with C = 2 + 1.5 * T/M;
  * the branching inequality exp(-c w_v) + exp(-c c_v) >= 1 at a minimizing vertex, c = 1/(3C);
  * F_G(p) >= (1/4) sum (log y)^2 / y for p_v = log y_v / y_v, y_v = d_v + 16.
Single process, at most a few seconds.
"""
import itertools, math, random

random.seed(134)


def F(adj, w):
    s = sum(x * (1 - math.log(x)) if x > 0 else 0.0 for x in w)
    return s - sum(w[u] * w[v] for u, v in edges(adj))


def edges(adj):
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


def maximize(adj, starts=6, iters=4000):
    n, best = len(adj), None
    for _ in range(starts):
        w = [random.uniform(0.01, 1.0) for _ in range(n)]
        for _ in range(iters):  # damped fixed point of w_v = exp(-w(N(v)))
            w = [0.5 * w[v] + 0.5 * math.exp(-sum(w[u] for u in adj[v])) for v in range(n)]
        val = F(adj, w)
        if best is None or val > best[0]:
            best = (val, w)
    return best


def count_ind(adj):
    n, c = len(adj), 0
    for mask in range(1 << n):
        if all(not (mask >> u & 1 and mask >> v & 1) for u, v in edges(adj)):
            c += 1
    return c


def has_k4(adj):
    n = len(adj)
    return any(all(b in adj[a] for a, b in itertools.combinations(q, 2))
               for q in itertools.combinations(range(n), 4))


def main():
    checked = 0
    for trial in range(60):
        n = random.randint(4, 11)
        p = random.uniform(0.2, 0.7)
        adj = [set() for _ in range(n)]
        for u, v in itertools.combinations(range(n), 2):
            if random.random() < p:
                adj[u].add(v); adj[v].add(u)
        if has_k4(adj):
            continue
        Fstar, w = maximize(adj)
        W = sum(w)
        M = sum(w[u] * w[v] for u, v in edges(adj))
        T = sum(w[a] * w[b] * w[c] for a, b, c in itertools.combinations(range(n), 3)
                if b in adj[a] and c in adj[a] and c in adj[b])
        stat = max(abs(math.log(1 / w[v]) - sum(w[u] for u in adj[v])) for v in range(n))
        assert stat < 1e-6, stat
        B = T / M if M > 0 else 0.0
        C = 2 + 1.5 * B
        cost = []
        for v in range(n):
            A = {v} | adj[v]
            cost.append(sum(w[a] for a in A) + sum(w[a] * w[b] for a, b in edges(adj) if a in A and b in A))
        avg = sum(w[v] * (cost[v] - C * (1 + math.log(1 / w[v]))) for v in range(n)) / W
        assert avg <= 1e-9, avg
        v = min(range(n), key=lambda x: cost[x] - C * (1 + math.log(1 / w[x])))
        c = 1 / (3 * C)
        assert math.exp(-c * w[v]) + math.exp(-c * cost[v]) >= 1 - 1e-12
        # single-vertex deletion identity F(q) = F* - w_v
        q = list(w); q[v] = 0.0
        assert abs(F(adj, q) - (Fstar - w[v])) < 1e-9
        y = [len(adj[x]) + 16 for x in range(n)]
        pt = [math.log(t) / t for t in y]
        assert F(adj, pt) >= 0.25 * sum(math.log(t) ** 2 / t for t in y) - 1e-12
        assert math.log(count_ind(adj)) >= Fstar / (3 * C) - 1e-9
        checked += 1
    print("checked", checked, "K4-free random graphs: all inequalities hold")


if __name__ == "__main__":
    main()
