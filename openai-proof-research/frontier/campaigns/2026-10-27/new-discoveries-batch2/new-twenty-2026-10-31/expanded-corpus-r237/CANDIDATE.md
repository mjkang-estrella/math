# No qualifying candidate

No result from this lane is submitted for acceptance or Lean formalization.

## Rejected q-matroid diagnostic: 352083

Over `F_8 = F_2[t]/(t^3+t+1)`, the matrix

```
1 0 0 t
0 1 t 0
```

gives circuit-relation nontransitivity both in the represented q-matroid and its dual. With bit-mask vectors, `(1,4,3)` is a nontransitivity witness in each. The full computed ranks and circuits are in `outputs/q-nondegenerate-candidate.json`.

This is **excluded**: the source's Example 21 already prints the corresponding q-matroid as its second matrix over `F_64`, with modulus `t^6+t^4+t^3+t+1` and rows `(1,t,0,0)`, `(0,0,1,t^8)`. The `F_2`-linear map whose basis images are `(1,12,4,3)` sends every subspace to a subspace with identical rank. All 67 comparisons are checked in `scripts/qcompare.py`. This is stronger subsumption evidence than merely matching the number of circuits. It disqualifies the construction regardless of whether the conjecture is literally refuted by that printed example. No novelty claim is made for the reduction, matrix, or failure mechanism.

## Eventown exact diagnostic: 352005

For even `n`, the all-ones vector is in the radical of the even-weight subspace's dot product. Thus even sets pair with their complements, with identical external odd-intersection adjacency and no adjacency inside a pair. At `n=6` this leaves 16 twin classes, each usable zero, one or two times.

For a fixed total family size, an optimum can be chosen with at most one singly used twin class. If classes `i,j` are both single, change their multiplicities by `(1,-1)` or `(-1,1)`. The sum of the two changes in the quadratic edge count is `-2 a_ij <= 0`. At least one direction does not increase the count, and reduces the number of single classes by two. Iteration proves the reduction. This is an ordinary mathematical reduction, not a Lean theorem.

The reduced exhaustive search covers respectively 48,048, 8,008, 80,080 and 11,440 multiplicity patterns for sizes 11, 12, 13 and 14. The exact minima are 12, 16, 20 and 24, agreeing with the conjecture. For larger families on the same ground set, taking a subfamily of the required size preserves a lower bound on the number of odd pairs. This verifies only the `n=6` parameter instance, which earns zero campaign credit. The remaining universal inequality is unproved here.

## Further work not claimed

The path-line computations leave growth-cap and iteration-cap cases unresolved and do not supply a minimality certificate. The trace-code computation is subsumed by a September 2026 proof. No literal endpoint, ordinary full-scope proof, independent review, paper or root acceptance exists for this lane. Do not count its finite diagnostics as solutions.
