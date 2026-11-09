"""In-lane independent recount of the n=5 witness counts.

Strict-index order-isomorphic containment (published AJC 94(2) 2026 p.280 reading):
w contains p iff some strictly increasing position tuple extracts a subsequence
order-isomorphic to p (order AND ties preserved, both directions).
Written fresh in this lane before the Lean build; compared against
frozen/review.md expectations: total 541, avoid(1122)=520, avoid(1112)=522.
"""
from itertools import combinations, product


def std_ranks(word):
    vals = sorted(set(word))
    rank = {v: i + 1 for i, v in enumerate(vals)}
    return tuple(rank[x] for x in word)


def contains(p, w):
    k = len(p)
    if k == 0 or len(w) < k:
        return k == 0
    ps = std_ranks(p)
    for idx in combinations(range(len(w)), k):
        if std_ranks([w[i] for i in idx]) == ps:
            return True
    return False


def packed_words(n):
    out = []
    for tup in product(range(1, n + 1), repeat=n):
        s = set(tup)
        if s == set(range(1, max(s) + 1)):
            out.append(tup)
    return out


W = packed_words(5)
print("total packed length-5 words:", len(W))
pW = (1, 1, 2, 2)
qW = (1, 1, 1, 2)
avoid_p = [w for w in W if not contains(pW, w)]
avoid_q = [w for w in W if not contains(qW, w)]
print("avoid p=[1,1,2,2]:", len(avoid_p))
print("avoid q=[1,1,1,2]:", len(avoid_q))
print("contain p:", len(W) - len(avoid_p), "contain q:", len(W) - len(avoid_q))
assert len(W) == 541 and len(avoid_p) == 520 and len(avoid_q) == 522
assert len(avoid_p) < len(avoid_q)
print("MATCH: 541 / 520 / 522; 520 < 522 OK")
