# Expanded corpus r109 handback

**No Lean candidate.** All 20 reserved IDs have a disposition in [results.json](results.json). All credits are zero. No campaign counts, shared ledgers, other lanes or historical files were changed. There were no git operations, no child agents and no browser tabs, and no background job is left running.

The pass did produce one complete ordinary proof of a literal conjecture, two exact new reductions, and computational coverage well beyond the source ranges. None of these qualifies under the credit standard.

## Outcomes by class

| Class | IDs |
|---|---|
| Full proof found, routine classical bridge (expected exclusion) | 338214 |
| Known: published or source-reported resolution | 344724 (Miyazaki 2205.01409, Thm 5.2), 344665 (proved in the source itself), 341618 (source's "note added in proof") |
| Parked with new finite coverage beyond the source | 338260, 339411, 343098, 343100, 343101, 344001, 348918 |
| Parked with diagnostics against the conjecture | 338569 |
| Parked with a partial reduction | 342411 |
| Parked: famous, analytic or asymptotic, or Lean-infeasible | 339492, 341964, 344132, 344430, 345005, 348339, 349132 |

## Main findings

* **338214 (MDS-PIR characterization): proved, but routine.** With κ/ν = k/n, every row of Λ must be exactly an information set. Condition (5) is equivalent to r(Z) ≥ k|Z|/n for every coordinate set Z (Wei-type duality via the subcode vanishing on Z). Edmonds' matroid covering theorem, applied to κ₀ parallel copies of each coordinate, then gives ν₀ disjoint bases. These form an MDS-PIR capacity-achieving matrix. The proof is in [PIR-PROOF.md](PIR-PROOF.md), with a 275-code LP cross-check in [outputs/pir-check.json](outputs/pir-check.json). The companion arXiv versions through Feb 2019 still call this open. It is a one-step bridge from a classical theorem, so it falls under the routine exclusion (compare 334207, 369221, 371637). No Lean was attempted: mathlib lacks matroid covering theory. Root may still wish to rule on it.
* **344724 (odd-cycle toric h-vector): known.** I found a short independent proof via Ehrhart reciprocity before the prior-art check. Interior points of kQ shift to points of (k−3)Q plus Σ_{r=1}^{s−2} C(m−2r+2s, 2s) slack-bijection points, which gives exactly rev(h) − h = Σ_{i=2}^{2s−3} (−t)^i. Miyazaki (arXiv 2205.01409, Theorem 5.2) already proved the conjecture, so this is zero credit.
* **344001 (six-element extreme sets): near-complete computational classification.** Extremality is equivalent to unimodular masses with μ∗μ̃ = 6δ₀. So every nonzero difference must repeat, and for full-rank coincidence patterns a Hadamard bound gives n ≤ 181. A complete canonical enumeration for n ≤ 181 found 1,487 candidate sets. Numerical solving recovers only Z₆ and {0,1,2,3,4,7} ⊂ Z₁₀. The source searched only orders ≤ 29.
  * **Source error:** Proposition 7.11's claimed extreme set {0,1,2,3,4,7} ⊂ Z₁₄ is not extreme, because difference 5 occurs once.
  * **Remaining gaps:** exact solvability, the rank-deficient patterns, and Lean infeasibility.
* **338569 (magic n₃-configurations): evidence against the conjecture.** The source's forbidden substructures have Levi cyclomatic number ≥ 3, so their expected count is O(n⁻²). Random configurations tested with the source's own criterion are magic in 28/30 cases at n = 100 and 12/12 at n = 150, while about 90% are non-magic at n ≤ 40. This suggests the proportion tends to 1, not 0. A rigorous refutation needs random-matrix cokernel theory, which is out of scope.
* **348918 (n-Queens integer spectrum).**
  * **Exact reduction:** A(Q(n)) = NNᵀ − 4I, where N is the square/line incidence matrix. So all non-(−4) eigenvalues come from a (6n−2)-dimensional Gram matrix.
  * **Coverage:** the conjecture holds for every n from 4 to 400 (floating diagnostic, minimum non-integer gap ≥ 1e-3), against the source's n ≤ 100. An earlier loose-tolerance run produced spurious hits; exact modular nullity confirmed they were artefacts. That run is retained and labelled superseded.
* **338260 (Catalan graph determinant).**
  * **Coverage:** det(CG_n) ≠ 0 for every odd n from 65 to 1999. A nonzero residue mod a prime is a rigorous certificate, given correct code.
  * **Structure:** odd-order determinants have the form ±2c² with irregular c.
  * **Literal defect:** det(CG₁) = 0, an endpoint defect with zero credit.
* **339411 (descent-polynomial disk).** No violation for all 1,048,575 sets I with max I ≤ 20, nor for |I| ≤ 2 up to m = 30. The source checked m ≤ 13. Jiradilok–McConville prove only the weaker Diaz-Lopez bounds.
* **343098 / 343100 / 343101 (equational graphs).** The counter reproduces the source's Table 1. New primes beyond the source's 3041: linear p = 3049 gives U₁ = 762 = L; cubic p = 3083 gives U₃ = 771 = L. Every unconnected graph has exactly two components.
* **342411 (uniquely-Wilf).** |F₄| = 23 is impossible by a one-line balance argument, and |F₄| = 22 has 5 balanced labelled choices. The F₄ = S₄ ILP timed out at level 6. An infeasibility certificate would also not be kernel-checkable without native evaluation.

## Prior-art and registry screens

* **Registries.** OpenAI/math HEAD is still `4eaee875…`. Omega HEAD has moved to `71b4592f31a0ce564acedcbee195fbd50f30bd8c` (2026-11-02T18:36Z), 369 commits after the root-known `01b573fd…`.
  * **New commits:** the compare API covers only the first 300 changed files (path screen); none contains a reserved ID.
  * **New tree:** the recursive tree response is truncated and lacks Problems/. A topic keyword path screen found nothing relevant; the matches were ArrowWilf, Sidon sets, Bajnok–Beatty and quantum "magic".
  * **Root's cached complete D5/Problems trees** (digits-parent-prior-art/registries): no ID or topic hits.
  * These are path screens, not proof reading.
* **Web.** Bounded web searches are dated 2026-11-02, with no 403/429 retries. Primary bodies read: the 1912.01212 abstract page, Miyazaki 2205.01409 Section 5, Jiradilok–McConville 1910.14631, and the 1712.03898v4 conjecture text. All HTTP receipts are in [sources/](sources/).

## Reproducibility

* **Extraction:** [scripts/extract.py](scripts/extract.py) copies r108's extractor; rg is unavailable, so it uses GNU grep with the same include globs. Exact raw lines are in [raw/](raw/), and [outputs/provenance-validation.json](outputs/provenance-validation.json) checks chunk hashes against the r301 manifest (`all_ok: true`).
* **Executables:** C programs (catalan_det, extreme6, extreme6b, equational) were compiled with the Lean toolchain's `leanc -O3`, header-free with explicit prototypes, because the host has no gcc.
* **Resource caps:** every expensive run used [scripts/limited.py](scripts/limited.py) (2 CPUs, CPU 120 s, wall 140 s, sampled RSS 6 GiB). Receipts are in [logs/](logs/). Runs stopped by the CPU cap are disclosed in results.json.
* **Uncapped incidents:**
  * One early descent-disk sweep was moved to the background and stopped manually.
  * One uncapped validation loop of the equational counter (p = 31, 107, 3041) was stopped after about 2 minutes.
  * Neither left a process behind or produced data.
* **Re-running:** [run.sh](run.sh) regenerates results.json and the provenance validation.

All numerical searches are diagnostics, except where noted as rigorous (nonzero modular determinants). No result here is self-accepted.
