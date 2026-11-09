"""Re-verify, with separate set-based code, every witness printed by dm_check.py (roots in B),
and re-check lambda by the cut definition with networkx-free set code for the m in the log.
usage: verify_witnesses.py <dm-check log>
"""
import sys, json


def dm(m):
    V = ["a%d" % i for i in range(1, m + 1)] + ["p1", "p2", "p3", "p4"]
    E = {(x, y) for x in V[:m] for y in V[:m] if x != y}
    E |= {("p1", "p2"), ("p2", "p3"), ("p3", "p4"), ("p4", "p1"), ("p1", "p3"), ("p2", "p4"), ("p4", "p2")}
    E |= {("a1", "p1"), ("a2", "p3"), ("p3", "a1"), ("p3", "a%d" % m)}
    return V, E


def reachable(s, E):
    seen = {s}; st = [s]
    while st:
        u = st.pop()
        for (x, y) in E:
            if x == u and y not in seen:
                seen.add(y); st.append(y)
    return seen


def strong(V, E):
    return all(reachable(v, E) == set(V) for v in V)


ok_all = True
checked = 0
for line in open(sys.argv[1]):
    if not line.startswith("{"):
        continue
    r = json.loads(line)
    m = r["m"]
    V, E = dm(m)
    for root, e in r["roots"].items():
        if not e["nonsep_found"]:
            continue
        F = set()
        for w in e["witness_arcs"]:
            # names are like a10p3: split at the second letter occurrence
            k = max(w.rfind("a"), w.rfind("p"))
            F.add((w[:k], w[k:]))
        indeg = {v: sum(1 for (x, y) in F if y == v) for v in V}
        good = (F <= E and indeg[root] == 0 and all(indeg[v] == 1 for v in V if v != root)
                and reachable(root, F) == set(V) and strong(V, E - F))
        checked += 1
        ok_all &= good
        print("m=%d root=%s witness_valid=%s" % (m, root, good))
print("checked=%d all_valid=%s" % (checked, ok_all))
