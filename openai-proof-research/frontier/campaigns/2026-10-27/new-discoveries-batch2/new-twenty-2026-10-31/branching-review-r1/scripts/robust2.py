"""Companion-paper-style dense paddings of W1 (review lane, independent code).

arXiv:2003.02107 Proposition 23 pads a small obstruction W with a semicomplete S by adding ALL arcs
from S to one vertex and ALL arcs from one vertex to S.  This script tests the analogous dense
paddings of W1 by a complete digraph A on m vertices (m = 3, 4, 5):
  P1: all arcs A -> p1, all arcs p3 -> A
  P2: all arcs A -> p1 and A -> p3, all arcs p3 -> A
  P3: all arcs A -> p3, all arcs p3 -> A (note p1 then keeps in-degree 1, so lambda = 1)
  D : the candidate's sparse attachment (a1p1, a2p3, p3a1, p3am), for comparison
and reports lambda >= 2, alpha = 2 and the roots in A without a non-separating out-branching.
"""
import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from robust import two_arc_strong, alpha_is_2, has_nonsep, W1  # own review-lane code

res = {}
for m in (3, 4, 5):
    A = range(m)
    p = lambda i: m + i
    base = set((i, j) for i in A for j in A if i != j) | {(p(u), p(v)) for (u, v) in W1}
    pats = {
        "P1_all_to_p1_all_from_p3": {(a, p(0)) for a in A} | {(p(2), a) for a in A},
        "P2_all_to_p1_p3_all_from_p3": {(a, p(0)) for a in A} | {(a, p(2)) for a in A} | {(p(2), a) for a in A},
        "P3_all_to_p3_all_from_p3": {(a, p(2)) for a in A} | {(p(2), a) for a in A},
        "D_candidate": {(0, p(0)), (1, p(2)), (p(2), 0), (p(2), m - 1)},
    }
    for k, extra in pats.items():
        arcs = sorted(base | extra)
        n = m + 4
        tas = two_arc_strong(n, arcs)
        al = alpha_is_2(n, arcs)
        fail = [s for s in A if not has_nonsep(n, arcs, s)] if tas else None
        res["m%d_%s" % (m, k)] = {"two_arc_strong": tas, "alpha_is_2": al,
                                   "failing_A_roots": None if fail is None else ["a%d" % (s + 1) for s in fail]}
print(json.dumps(res, indent=1, sort_keys=True))
