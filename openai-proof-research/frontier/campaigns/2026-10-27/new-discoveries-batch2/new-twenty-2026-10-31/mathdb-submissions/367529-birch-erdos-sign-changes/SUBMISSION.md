# MathDB 367529: The Birch–Erdős representation function f_{p,q} increases and decreases infinitely often (Ding–Liu–Wang Conjecture 3)

- Problem: https://mathdb.com/p/367529
- Source: Yuchen Ding, Honghu Liu and Zi Wang, “Note on a theorem of Birch and Erdős”, arXiv:2503.11676 (2025); J. Number Theory (2025), doi 10.1016/j.jnt.2025.07.009; Conjecture 3. https://arxiv.org/abs/2503.11676
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `Fpq.ding_liu_wang_conj3`, `Fpq.conj3`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The journal version (J. Number Theory, doi 10.1016/j.jnt.2025.07.009) and the one indexed citing paper (H. Liu, Period. Math. Hungar., doi 10.1007/s10998-026-00707-y) could not be read in full; arXiv v3 and the indexed journal preview still call the statement Conjecture 3, and the citing paper's abstract concerns a different question (reviewer's probability that it settles this conjecture: 0.02). The increases are the authors' own Corollary 3; the contribution is the decreases, a few compact paragraphs. Proof, first (same-model) review and Lean are by Claude Opus 5.5; the cross-model review and final check are by GPT-6.2 Sol (two rounds; not routine 0.58, close to the floor of 0.55 root uses for counting).
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Ding, Liu and Wang (arXiv:2503.11676, Conjecture 3) conjectured that for coprime q > p > 2 the Birch–Erdős representation function f_{p,q}(n), which counts representations of n as sums of distinct p^a q^b, changes direction infinitely often. It has infinitely many strict increases (from the authors' asymptotic) and infinitely many strict decreases (by a root-of-unity argument that fails exactly at p = 2, where f is monotone). The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $f_{p,q}(n)$ be the Birch–Erdős representation function, with $p$ and $q$ relatively prime integers satisfying $q>p>2$. **Sign-change conjecture.** The sign of

$$
f_{p,q}(n+1)-f_{p,q}(n)
$$

changes infinitely often. The conjecture is presented as a possible example of the Chebyshev bias phenomenon; the source does not establish it.

## Summary of the result

The conjecture holds: for all coprime q > p > 2, the difference f_{p,q}(n+1) − f_{p,q}(n) is strictly positive for infinitely many n and strictly negative for infinitely many n, where f_{p,q}(n) counts the representations of n as a sum of distinct numbers p^a q^b. Infinitely many increases follow from the authors' Corollary 3 (f is unbounded). The new part is the decreases: if f were eventually nondecreasing, a comparison at roots of unity would force certain twisted products over pure powers to vanish, while the exact product over all roots of unity gives a uniform lower bound; the contradiction needs p > 2 (for p = 2 the authors prove that f is monotone). Lean defines f by the source's literal representation count and proves both infinitely many strict increases and infinitely many strict decreases, with non-vacuity checks.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
