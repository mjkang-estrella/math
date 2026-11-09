# No qualifying candidate

No full literal Lean endpoint is proposed. All 20 dispositions are in `results.json`. The strongest unresolved leads remain 338456 (pointed e-positivity), 344793 (Clar unimodality) and 381476 (fixed-size independent-set extremality), with the finite coverage in `SUMMARY.md`. No negative instance was found for them.

## Excluded path diagnostic: 359351

Let T = P8, k = 3. One distance-3 guard covers at most seven vertices, and two suffice, so gamma_3(T) = 2. Divide the path into two consecutive four-vertex intervals. Keep one guard in each interval; each guard can move to any attacked vertex in its interval in at most three steps, and each interval remains dominated. Thus the eternal distance-3 number is 2. Ordinary domination is 3: two closed neighborhoods cover at most six vertices, while vertices 2,5,8 dominate.

The antecedent of the reserved conjecture holds, but its conclusion fails, since floor(3/2) = 1. The program found all 16 minimum distance-3 configurations winning.

This is **excluded**, not submitted as a new result. Cox–Meger–Messinger, arXiv:2104.03835, Theorem 2 already proves eternal distance-k domination of P_n equals ceiling(n/(k+1)); the source cites that result. The remaining ordinary domination calculation is elementary. Generalizing to odd k with P_(2k+2) would remain the same source-formula bridge. A Lean formalization would not restore eligibility.

## Excluded elementary completion observation: 338449

Under Definition 2.1 of the cited source, completeness means product is a positive integer multiple of sum. For a finite positive set T, write S for its sum and P for its product. If P >= 3, x = S(P-1) exceeds every element of T and

```
product(T union {x}) = P S(P-1)
sum(T union {x}) = SP.
```

The multiplier is P-1. If P = 2, T is {2} or {1,2}, and extending to {1,2,3} suffices; the empty set and {1} are also contained there. This is too elementary for campaign credit. Moreover, the named completion conjecture was not found in either retrieved arXiv version; their conjecture concerns counting complete subsets. No substitute counting result or source-fidelity resolution is claimed.
