#!/usr/bin/env python3
"""MIT. Round-2 reviewer recomputation, written from source 02-counts.tex definitions
and candidate section 1; imports no author or round-1 code. Diagnostic only, not proof.
Recomputes W for (a) the naive symmetric recursion (orbit max, even fixed rounding,
ordinary k+1 rules) and (b) the candidate rule (2k+1 for self-reversed texts),
and OPT_RC by exhaustive search, on identity involution and S={bbcbbc,bcbbcb,cbbcbb}."""
import itertools, json, sys

def rho(s, cm):
    return ''.join(cm[c] for c in reversed(s))

def counts(S, cm, strong):
    S = [s for s in S if s]
    orbits = {min(s, rho(s, cm)) for s in S}
    orbits = {o for o in orbits if not any(o != x and (o in x or o in rho(x, cm) or rho(o, cm) in x) for x in orbits)}
    R = set(orbits) | {rho(o, cm) for o in orbits}
    V = {r[i:j] for r in R for i in range(len(r) + 1) for j in range(i, len(r) + 1)}
    Sig = sorted({c for r in R for c in r})
    m = {}
    def b(Aper, s, r):
        # Aper: function index->letter, s = A[0:|s|)
        n = 0
        for j in range(1, len(r) - len(s)):
            if r[j:j + len(s)] != s:
                continue
            if all(r[h] == Aper(h - j) for h in range(1, len(r) - 1)) and r[0] != Aper(-j) and r[-1] != Aper(len(r) - 1 - j):
                n += 1
        return n
    def B(Aper, s):
        return sum(b(Aper, s, r) * m.get(r, 0) for r in V if len(r) >= len(s) + 2)
    def selfrev(base):
        p = len(base); A = lambda i: base[i % p]
        rb = rho(base, cm)
        return any(all(rb[i] == A(i + d) for i in range(p)) for d in range(p))
    # rules indexed by target w: list of (v, base)
    rules = {}
    for v in V:
        for p in range(1, len(v)):
            base = v[:p]
            if any(v[i] != base[i % p] for i in range(len(v))):
                continue
            k = 1
            while k * p < len(v):
                rules.setdefault(v[:len(v) - k * p], []).append((v, base, k))
                k += 1
    for L in range(max(map(len, V)), 0, -1):
        layer = sorted(s for s in V if len(s) == L)
        lb = {}
        for s in layer:
            x = max(sum(m.get(c + s, 0) for c in Sig), sum(m.get(s + c, 0) for c in Sig))
            if s in R:
                x = max(x, 2 if s == rho(s, cm) else 1)
            for (v, base, k) in rules.get(s, []):
                A = (lambda bs: (lambda i: bs[i % len(bs)]))(base)
                if m[v] > B(A, v):
                    g = (2 * k + 1) if (strong and selfrev(base)) else (k + 1)
                    x = max(x, B(A, s) + g)
            lb[s] = x
        for s in layer:
            x = max(lb[s], lb[rho(s, cm)])
            if s == rho(s, cm) and x % 2:
                x += 1
            m[s] = x
    return sum(m[c] for c in Sig if c in m), m

def opt_rc(S, cm, alphabet):
    S = [s for s in S if s]
    for n in itertools.count(0):
        for t in itertools.product(alphabet, repeat=n):
            T = ''.join(t)
            if all(s in T or rho(s, cm) in T for s in S):
                return n, T

if __name__ == '__main__':
    cm = {'b': 'b', 'c': 'c'}
    S = ['bbcbbc', 'bcbbcb', 'cbbcbb']
    wn, mn = counts(S, cm, False)
    ws, ms = counts(S, cm, True)
    o, T = opt_rc(S, cm, 'bc')
    out = {'instance': S, 'involution': 'identity on {b,c}', 'W_naive_symmetric': wn,
           'W_selftext_2k_plus_1': ws, 'OPT_RC': o, 'witness': T,
           'naive_counts': {k: v for k, v in sorted(mn.items(), key=lambda kv: (-len(kv[0]), kv[0])) if k},
           'status': 'DIAGNOSTIC_ONLY'}
    print(json.dumps(out, indent=1, sort_keys=True))
    ok = wn == 6 and o == 7 and ws <= 2 * o and ws >= o
    sys.exit(0 if ok else 1)
