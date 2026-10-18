#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Finite illustration of the reviewer's unweighted remark in review.md, section 4.

States: deletion words p with 1<=|p|<=m, one shared empty state, creation words
q with 1<=|q|<=n. Letter x deletes a leading x from p, and appends x to q.
The (q,p) entry of a word w is 1 iff w = q.p, so distinct words of length
<= m+n have disjoint nonempty supports and longer words vanish. This script
checks that statement for r=2, m=n=4 (61 states). It is an illustration only;
the review relies on the three-line proof, not on this finite check.
"""
import itertools
import json

R, M, N = 2, 4, 4
letters = range(R)
words = lambda k: list(itertools.product(letters, repeat=k))
states = [("P", w) for k in range(M, 0, -1) for w in words(k)] + [("E", ())] + \
         [("Q", w) for k in range(1, N + 1) for w in words(k)]
index = {s: i for i, s in enumerate(states)}


def step(state, x):
    kind, w = state
    if kind == "P":
        if w[0] != x:
            return None
        return ("P", w[1:]) if len(w) > 1 else ("E", ())
    nxt = w + (x,)
    return ("Q", nxt) if len(nxt) <= N else None


def support(word):
    """Entries (source, target) with value 1; letters act right to left."""
    out = set()
    for s in states:
        cur = s
        for x in reversed(word):
            cur = step(cur, x)
            if cur is None:
                break
        if cur is not None:
            out.add((index[s], index[cur]))
    return out


seen = {}
for k in range(1, M + N + 1):
    for w in words(k):
        sup = support(w)
        assert sup, w
        for entry in sup:
            assert entry not in seen, (w, seen.get(entry))
            seen[entry] = w
for w in words(M + N + 1):
    assert not support(w)
print(json.dumps({"states": len(states), "words_checked": sum(R ** k for k in range(1, M + N + 1)),
                  "longer_words_vanish": True, "disjoint_supports": True,
                  "status": "ILLUSTRATION_PASS_NOT_PROOF"}))
