# Mathematical attempts (r67)

All runs use `scripts/limited.py` or `scripts/leanrun.py`: 2 CPUs, CPU 120 s, wall 140 s, sampled RSS 6 GiB. Logs and receipts are in `logs/`. Numerical runs are diagnostics only.

## 371639 — Clow–Kumar–Pragada Conjecture 7.5 (REFUTED; Lean endpoint)

See `PROOF-371639.md`. Route: a fractional lower bound from a C₅ lexicographic power, plus padding, which inflates |V(H)|. A hub variant makes the counterexample connected. Both are formalised: `not_conjecture` and `not_connectedConjecture`. The fresh strict replay passes (`lean/fresh-replay-r1/replay-receipts/result.json`).

## 372105 — panchromatic / bipanchromatic equality (known)

Mechanism: unique colours must lie in the intersection of all edges. With core {1,2,3} and edges {1,2,3,x} for x = 4,5,6, we get χ_p = 4 and α = 3, so the formula gives 2, but χ²_p = 3. `scripts/panchromatic.py` (outputs/panchromatic.json) confirms this. An exhaustive check of every hypergraph on at most 5 vertices with at most 3 edges (sizes ≥ 2) found no counterexample, consistent with 6 vertices being minimal. Prior-art check then found the conjecture already refuted: arXiv:2610.08042 (by the source authors, 2026-10-06), arXiv:2610.27133 (the smallest counterexample has 6 vertices and 3 edges), Omega D5 `S3/ConceptDynamics/GraphColoring/PanchromaticPairingConjectureRefutation.lean`, and Omega issue #8518. Excluded as known.

## 372569 — Jovović–Koledin–Stanić spectral gap of trees (sustained, parked)

`scripts/tree_gap.py` enumerates all non-isomorphic trees for 4 ≤ n ≤ 19 (vendored NetworkX copy, numpy eigvalsh). The minimiser of λ₁ − λ₂ is always a balanced double comet DC(k,k,ℓ): paths for n ≤ 8, then k = 2, 3, 4 as n grows. Floating-point results are in outputs/tree_gap.json; no counterexample. A proof would need the source's perturbation machinery; parked.

## 372373 — (3,4)-tournament spanning paths (sustained, parked)

- `scripts/tour34_sat.py`: direct CNF (exactly 4 of 6 orderings per triple; one blocking clause per permutation), solved with the cadical bundled with Lean. Without symmetry breaking, n = 7 and n = 8 hit the 120 s CPU cap. n = 7 is already verified in the literature (Lavrov).
- `scripts/tour34_local.py`: hill climbing on the exact DP count of spanning paths for n = 8 over 110 s and 550 restarts. Its best was 1442 spanning paths, far above the known construction with 2^(n−1) = 128, so the search is too weak to be evidence either way.
- Next step, not done: isomorph-free orderly generation or a symmetry-broken incremental SAT encoding.

## 371679 — saturation numbers of K_s ∨ P_k (partial, known case)

K_s ∨ P_3 = K_{s+3} − e. Faudree–Gould (Graphs Combin. 29 (2013) 429–448), Theorem 9(i) (PDF fetched, `sources/faudree-gould-P154Y13.pdf`): sat(n, K_t − e) = ⌊(2t−5)(n−t+3)/2⌋ + C(t−3,2) for n ≥ t. With t = s+3 this equals C(s,2) + s(n−s) + ⌊(n−s)/2⌋, the conjectured value, since sat(m, P_3) = ⌊m/2⌋. So k = 3 is known and gives no counterexample; k ≥ 4 is open and was not pursued.

## Other screens

- 372272 is confirmed in its own source. 372551 is a theorem by Bamler–Lai, as the source states. 372394 was refuted for all p ≥ 4 by Char–Maniya–Pradhan and Clow–Zaguia, as cited in the source.
- 371701: the smallest open Frankl–Kupavskii case has n = 17, which is infeasible to compute.
- 372117: Ramsey bounds leave k = 6 undecidable.
- 371617: a refutation needs n > 100, and generation certificates are heavy.
- The remaining items are famous or structural conjectures with no finite certificate; they are recorded compactly in results.json.
