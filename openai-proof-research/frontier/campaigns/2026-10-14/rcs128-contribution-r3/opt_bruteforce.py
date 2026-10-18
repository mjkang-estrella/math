#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Reviewer-written exhaustive OPT_RC check for the two motivation instances (finite diagnostic, not a proof of the candidate)."""
import itertools, json


def rho(word, cm):
    return ''.join(cm[ch] for ch in reversed(word))


def feasible(text, family, cm):
    return all(s in text or rho(s, cm) in text for s in family)


def opt_rc(family, cm, alphabet):
    for n in range(0, sum(map(len, family)) + 1):
        hits = [''.join(t) for t in itertools.product(alphabet, repeat=n) if feasible(''.join(t), family, cm)]
        if hits:
            return n, hits[0], len(hits)


cases = [
    {"name": "identity-involution template obstruction", "family": ["bbcbbc", "bcbbcb", "cbbcbb"], "cm": {"b": "b", "c": "c"}},
    {"name": "composite-route tie-breaking instance", "family": ["aaa", "aab", "abcaa", "accc"], "cm": {"a": "b", "b": "a", "c": "c"}},
]
out = []
for c in cases:
    n, witness, count = opt_rc(c["family"], c["cm"], sorted(c["cm"]))
    out.append({"name": c["name"], "family": c["family"], "involution": c["cm"], "OPT_RC": n, "first_witness_lexicographic": witness, "optimal_words": count})
print(json.dumps(out, indent=1, sort_keys=True))
