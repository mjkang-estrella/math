"""Explore for a Lyapunov function: a statistic Phi with
Phi(s(pi)) < Phi(pi) for all pi not in {id,rev} (edges within {id,rev} exempt),
or an analogous increase. Also inspect orbit structure.
"""
import sys, os, json, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lib_sT import s_T, reverse_word

T1 = ((1, 3, 2), (2, 1, 3))
T2 = ((2, 3, 1), (2, 1, 3))

def inv(p):
    return sum(1 for i in range(len(p)) for j in range(i + 1, len(p)) if p[i] > p[j])

def noninv(p):
    n = len(p)
    return n * (n - 1) // 2 - inv(p)

def disp(p):  # sum |pi_i - i|
    return sum(abs(v - i - 1) for i, v in enumerate(p))

def disp2(p):
    return sum((v - i - 1) ** 2 for i, v in enumerate(p))

def desc(p):
    return sum(1 for i in range(len(p) - 1) if p[i] > p[i + 1])

def maj(p):
    return sum(i + 1 for i in range(len(p) - 1) if p[i] > p[i + 1])

def lis(p):
    n = len(p)
    best = [1] * n
    for i in range(n):
        for j in range(i):
            if p[j] < p[i]:
                best[i] = max(best[i], best[j] + 1)
    return max(best)

def lds(p):
    return lis(tuple(-v for v in p))

def nrmc(p):  # number of non-inversions... already have; add "sum of max-plus"
    pass

STATS = {"inv": inv, "noninv": noninv, "disp": disp, "disp2": disp2,
         "desc": desc, "maj": maj, "lis": lis, "lds": lds}

def explore(T, n, name):
    ident = tuple(range(1, n + 1)); rev = reverse_word(ident)
    cyc = {ident, rev}
    strict_dec = {k: 0 for k in STATS}
    strict_inc = {k: 0 for k in STATS}
    equal = {k: 0 for k in STATS}
    edges_outside = 0
    violations = {k: [] for k in STATS}
    for pi in itertools.permutations(range(1, n + 1)):
        if pi in cyc:
            continue
        sp = s_T(pi, T)
        if sp in cyc:
            continue  # edges into the cycle: monotone ok but check anyway below
        edges_outside += 1
        for k, f in STATS.items():
            a, b = f(pi), f(sp)
            if b < a:
                strict_dec[k] += 1
            elif b > a:
                strict_inc[k] += 1
            else:
                equal[k] += 1
            if not (b < a) and len(violations[k]) < 3:
                violations[k].append((pi, sp, a, b))
    print(f"== {name} n={n}: edges outside cycle: {edges_outside}")
    for k in STATS:
        print(f"  {k}: dec {strict_dec[k]} inc {strict_inc[k]} eq {equal[k]}")
    return {k: {"dec": strict_dec[k], "inc": strict_inc[k], "eq": equal[k]} for k in STATS}

res = {}
for name, T in (("132_213", T1), ("231_213", T2)):
    for n in (5, 6):
        res[f"{name}_n{n}"] = explore(T, n, name)
json.dump(res, open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                                 "work", "lyapunov-scan.json"), "w"), indent=1)
