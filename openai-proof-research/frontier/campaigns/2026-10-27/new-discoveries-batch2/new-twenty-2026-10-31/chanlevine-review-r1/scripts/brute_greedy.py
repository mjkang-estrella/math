"""Tier-2 count of recurrent configurations by FORWARD DYNAMICS, via the source's stated
characterization Lemma 5.3(iii) of arXiv:1804.03322v2 (independent of lane r127 and of the cycle test):

  x.q is recurrent  iff  there is a legal execution w for x.q with |w| = r and t_w q = q,

where r is the period vector (Definition 5.1).  For the sinkless rotor network on C_n the production
matrix is P = A D^{-1} = A/2, its Perron eigenvector is constant, and the total kernel is
K = {z : z(v) even} (Example 3.11), so r = (2, ..., 2); t_w q = q is then automatic (each rotor flips
twice).

Search for such a w: fire, greedily, any vertex v with x(v) >= 1 that has fired fewer than 2 times,
until stuck.  Exactness: if some legal w with |w| = r exists and the greedy word u gets stuck with
|u| <= r, |u| != r, then by the removal lemma (Lemma 4.2) w \\ |u| is legal for pi_u(x.q); its first
letter is a vertex with a chip and fewer than 2 firings, contradicting stuckness.  So recurrent iff
the greedy run reaches |u| = r.  Chips are only ever needed up to 2 per vertex: each vertex fires at
most twice, so replacing x by min(x, 2) does not change any greedy decision (if x(v) >= 2 then before
its second firing v holds >= 1 chip either way).  Hence the test depends only on (min(x,2), q).

Processing rule (Example 3.11): flip the rotor first, then move the chip along the NEW rotor.
Weight (Section 8.3): wt = sum_k k x(k) + #{k : rotor of v_k points to v_{k-1}}  (mod n).

Usage: python3 -I brute_greedy.py OUT.json n mmax [--literal]
  --literal : additionally run the greedy on the literal (uncapped) x for every configuration
              and check it agrees with the capped test (only for small n).
"""
import itertools
import json
import sys
import time


def greedy_recurrent(x, qm, n):
    x = list(x)
    cnt = [0] * n
    progress = True
    while progress:
        progress = False
        for v in range(n):
            while x[v] >= 1 and cnt[v] < 2:
                qm ^= (1 << v)                       # advance rotor
                t = (v + 1) % n if (qm >> v) & 1 else (v - 1) % n
                x[v] -= 1
                x[t] += 1
                cnt[v] += 1
                progress = True
    return all(c == 2 for c in cnt)


def compositions(n, m):
    if n == 1:
        yield (m,)
        return
    for a in range(m + 1):
        for rest in compositions(n - 1, m - a):
            yield (a,) + rest


def main():
    out = sys.argv[1]
    n = int(sys.argv[2])
    mmax = int(sys.argv[3])
    literal = "--literal" in sys.argv
    t0 = time.process_time()
    Q = 1 << n
    minus = [sum(1 for k in range(n) if not (qm >> k) & 1) for qm in range(Q)]
    H = {}
    for c in itertools.product((0, 1, 2), repeat=n):
        h = [0] * n
        for qm in range(Q):
            if greedy_recurrent(c, qm, n):
                h[minus[qm] % n] += 1
        H[c] = h
    t1 = time.process_time()
    results = []
    lit_mismatch = 0
    lit_checked = 0
    for m in range(1, mmax + 1):
        A = {}
        for x in compositions(n, m):
            c = tuple(min(a, 2) for a in x)
            s = sum(k * x[k] for k in range(n)) % n
            A[(c, s)] = A.get((c, s), 0) + 1
            if literal:
                for qm in range(Q):
                    lit_checked += 1
                    if greedy_recurrent(x, qm, n) != greedy_recurrent(c, qm, n):
                        lit_mismatch += 1
        N = [0] * n
        for (c, s), cnt in A.items():
            h = H[c]
            for i in range(n):
                N[i] += cnt * h[(i - s) % n]
        res = {"n": n, "m": m, "r": N, "total": sum(N)}
        results.append(res)
        print(json.dumps(res), flush=True)
    summary = {"n": n, "mmax": mmax, "pattern_pairs_tested": 3 ** n * Q,
               "pattern_cpu_s": round(t1 - t0, 3), "total_cpu_s": round(time.process_time() - t0, 3)}
    if literal:
        summary["literal_checked"] = lit_checked
        summary["literal_mismatch"] = lit_mismatch
    print(json.dumps(summary))
    with open(out, "w") as f:
        json.dump({"summary": summary, "results": results}, f, indent=1)


if __name__ == "__main__":
    main()
