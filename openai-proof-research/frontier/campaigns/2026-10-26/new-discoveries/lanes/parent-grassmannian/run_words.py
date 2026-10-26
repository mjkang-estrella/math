"""Exploratory RREF column-run enumeration; classification proof pending.

Integer determinant arithmetic is exact. This is not a Grassmannian cardinality
theorem: completeness and the run-count/row-space bridge need proofs.
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations, permutations, product
from math import comb
from pathlib import Path
import json


def determinant(k):
    signed = [(p, (-1)**sum(p[i] > p[j] for i in range(k) for j in range(i+1,k)))
              for p in permutations(range(k))]
    @lru_cache(None)
    def det(cols):
        total = 0
        for p, sign in signed:
            term = sign
            for j in range(k):
                term *= cols[j][p[j]]
            total += term
        return total % 3
    return det


def extend(previous, k):
    det = determinant(k)
    pivot = tuple([0]*(k-1)+[1])
    candidates = [tuple(((-1)**(k-1-i)*x) % 3 for i,x in enumerate(xs))
                  for xs in product(range(2),repeat=k) if any(xs)]
    words = []
    def dfs(cols, remaining):
        words.append(cols)
        for v in remaining:
            if v == cols[-1]:
                continue
            if all(det(t+(v,)) != 2 for t in combinations(cols,k-1)):
                dfs(cols+[v], [w for w in remaining if w != v])
    for old in previous:
        prefix = [tuple(v)+(0,) for v in old]+[pivot]
        assert all(det(t) != 2 for t in combinations(prefix,k))
        eligible = [v for v in candidates if all(det(t+(v,)) != 2 for t in combinations(prefix,k-1))]
        dfs(prefix,eligible)
    return words


words = [[(1,)]]
records = []
for k in range(2,5):
    words = extend(words,k)
    counts = Counter(map(len, words))
    record = {"rank":k,"run_histogram":dict(sorted(counts.items())),
              "number_of_skeletons":len(words),"maximum_length":max(counts)}
    record["predicted_point_counts_NOT_PROVED"] = [
        {"n":n,"predicted_count":sum(c*sum(comb(n,m)*comb(m-1,l-1)
            for m in range(l,n+1)) for l,c in counts.items())}
        for n in range(k,13)]
    records.append(record)
    print(json.dumps(record),flush=True)
Path('run-words.json').write_text(json.dumps({"status":"Exploration only; complete classification not proved",
                                             "field":3,"records":records},indent=2)+'\n')
