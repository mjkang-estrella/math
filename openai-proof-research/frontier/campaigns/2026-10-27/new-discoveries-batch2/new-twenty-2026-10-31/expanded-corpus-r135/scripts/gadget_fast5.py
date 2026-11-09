"""Sharded b-vertex gadget search (reduced criterion of gadget_fast.py), bitmask cut tables.
Usage: gadget_fast5.py b shard nshards mindeg
Only D[B] with minimum in-degree >= mindeg inside B are considered.
"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(__file__))
from gadget_fast import fails

b, shard, nsh, mindeg = map(int, sys.argv[1:5])
pairs = list(itertools.combinations(range(b), 2))
full = (1 << b) - 1
cnt = tested = 0
hits = []
for idx, states in enumerate(itertools.product(range(3), repeat=len(pairs))):
    if idx % nsh != shard:
        continue
    arcs = []
    for (u, v), st in zip(pairs, states):
        if st in (0, 2):
            arcs.append((u, v))
        if st in (1, 2):
            arcs.append((v, u))
    indeg = [0] * b
    for (u, v) in arcs:
        indeg[v] += 1
    if min(indeg) < mindeg:
        continue
    cnt += 1
    internal = [0] * (1 << b)
    for Y in range(1 << b):
        internal[Y] = sum(1 for (u, v) in arcs if (Y >> u) & 1 and not (Y >> v) & 1)
    for e1, e2 in itertools.combinations_with_replacement(range(b), 2):
        emask = [((1 << e1) & Z != 0) + ((1 << e2) & Z != 0) for Z in range(1 << b)]
        for x1, x2 in itertools.combinations_with_replacement(range(b), 2):
            ok = True
            for Y in range(1 << b):
                Z = full ^ Y
                if Z and internal[Y] + emask[Z] < 2:
                    ok = False
                    break
                if Y and internal[Y] + ((1 << x1) & Y != 0) + ((1 << x2) & Y != 0) < 2:
                    ok = False
                    break
            if not ok:
                continue
            tested += 1
            if fails(b, arcs, e1, e2, [x1, x2]) and fails(b, arcs, e2, e1, [x1, x2]):
                hits.append((arcs, (e1, e2), (x1, x2)))
print('b', b, 'shard', shard, '/', nsh, 'mindeg', mindeg, 'digraphs', cnt, 'attachments tested', tested, 'hits', len(hits), flush=True)
for h in hits[:5]:
    print(h)
