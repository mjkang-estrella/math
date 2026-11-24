# MathDB 340621: The $3$-cube-free density conjecture in $\mathbb{Z}_{2^n}$

- Problem: https://mathdb.com/p/340621
- Source: Jason Long and Adam Zsolt Wagner, “The largest projective cube-free subsets of Z_2^n”, arXiv:1810.01225 (2018). https://arxiv.org/abs/1810.01225
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `LongWagner.lw_upper`, `LongWagner.lw_conj_5_1`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. An active area: Randjelovic, arXiv:2611.23559 (17 November 2026), proved the high-odd-density case three days earlier and left this interval open; a prior-art refresh on 2026-11-20 found no full earlier proof, but re-check arXiv before publishing. Equality holds for n >= 3 (the MathDB record omits that range; for n < 3 only the upper bound is meaningful). Computer-assisted: most of the 174 Lean modules are certificate data (about 20,800 generated lines) checked by one verified checker. The sibling record 340620 (the general-d conjecture) is not settled. The journal text of the source and a thesis could not be read. Cross-model confidence: correct 0.97, not public 0.85, not routine 0.8. No second cross-model lane read the finished Lean: root compared the cube definition and both endpoints with the ones that reviewer had written and found them identical.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. A subset of Z_{2^n} with no 3-dimensional cube {x, y, z, x+y, x+z, y+z, x+y+z} has size at most (5/8) 2^n, and for n >= 3 the maximum is exactly 5 * 2^(n-3). This is Conjecture 5.1 of Long and Wagner. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $n$ be a positive integer, and consider subsets of $\mathbb{Z}_{2^n}$ that contain no $3$-cube. **The $3$-cube-free density conjecture.** The largest $3$-cube-free family in $\mathbb{Z}_{2^n}$ has size $(5/8)\cdot 2^n$. Since $L_1\cup L_3$ is $3$-cube-free, the proposed bound would be sharp; the paper states that this is the first open case of the general optimality conjecture.

## Summary of the result

A subset A of the cyclic group Z_{2^n} that contains no 3-dimensional cube, that is no x, y, z (not necessarily distinct, zero allowed) with all seven nonempty subset sums in A, has at most (5/8) 2^n elements, and for every n >= 3 the maximum is exactly 5 * 2^(n-3). This is Conjecture 5.1 of Long and Wagner. The earlier upper bounds were 2/3 (Meng) and, three days before this result, a treatment of the case where the odd layer has density above 2/3 (Randjelovic), with the interval between 5/8 and 2/3 left open. The proof averages a certified weighted inequality for cube-free sets over odd multipliers, decomposes the density by 2-adic layers, treats the high-odd-density branch by a direct counting argument, and inducts over the subgroups 16Z and 32Z; the extremal example is the preimage of five residues modulo 8. The finite inequality is certified by one verified checker over 12,564 states and 1,441 cubes, with the coverage of all cases proved in Lean.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
