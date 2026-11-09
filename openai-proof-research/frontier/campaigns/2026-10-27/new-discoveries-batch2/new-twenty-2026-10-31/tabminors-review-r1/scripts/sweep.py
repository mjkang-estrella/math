"""Gate B check 2: exhaustive injectivity of T -> mM_k(T) on YT(n) for n = k + 4 and n = k + 5.

For each tableau S of size s we store the vector of mM_{s-t}(S) indexed by YT(t), for t = 4, 5,
using mM_{j+1}(S) = sum_m mM_j(S - m).  Level s is generated from level s-1 by adding the entry s.
Usage: python3 -I sweep.py <scripts dir> <N>
"""
import json
import sys
from collections import Counter, defaultdict

sys.path.insert(0, sys.argv[1])
from jdt import delete, all_syt  # noqa: E402

N = int(sys.argv[2])
TS = (4, 5)
idx = {t: {T: i for i, T in enumerate(all_syt(t))} for t in TS}


def grow(T, v):
    out = []
    rows = list(T)
    for i in range(len(rows) + 1):
        if i == len(rows):
            out.append(tuple(rows) + ((v,),))
        elif i == 0 or len(rows[i]) < len(rows[i - 1]):
            new = list(rows)
            new[i] = rows[i] + (v,)
            out.append(tuple(new))
    return out


def report(s, vecs, t):
    groups = defaultdict(list)
    for T, v in vecs.items():
        groups[v].append(T)
    coll = [g for g in groups.values() if len(g) > 1]
    return {
        "n": s, "k": s - t, "tableaux": len(vecs),
        "colliding_tableaux": sum(len(g) for g in coll),
        "collision_classes": len(coll),
        "examples": [sorted([list(map(list, T)) for T in g]) for g in coll[:2]],
        "set_version_colliding_tableaux": sum(
            len(g) for g in defaultdict(list, _sets(vecs)).values() if len(g) > 1),
    }


def _sets(vecs):
    d = defaultdict(list)
    for T, v in vecs.items():
        d[tuple(x > 0 for x in v)].append(T)
    return d


results = []
level = {}
for T in all_syt(min(TS)):
    level[T] = {t: None for t in TS}
for t in TS:
    pass
# Base: size 4 tableaux have mM_0 vector for t = 4; size 5 tableaux start t = 5.
cur = {}
for T in all_syt(4):
    v4 = [0] * len(idx[4]); v4[idx[4][T]] = 1
    cur[T] = (tuple(v4), None)
for s in range(5, N + 1):
    nxt = {}
    for P in cur:
        for T in grow(P, s):
            a4 = [0] * len(idx[4])
            if s == 5:
                a5 = [0] * len(idx[5]); a5[idx[5][T]] = 1
            else:
                a5 = [0] * len(idx[5])
            for m in range(1, s + 1):
                D = delete(T, m)
                v4, v5 = cur[D]
                for i, x in enumerate(v4):
                    a4[i] += x
                if s > 5:
                    for i, x in enumerate(v5):
                        a5[i] += x
            nxt[T] = (tuple(a4), tuple(a5))
    cur = nxt
    results.append(report(s, {T: v[0] for T, v in cur.items()}, 4))
    if s > 5:
        results.append(report(s, {T: v[1] for T, v in cur.items()}, 5))
    print(json.dumps(results[-2:] if s > 5 else results[-1:]), file=sys.stderr, flush=True)
print(json.dumps(results))
