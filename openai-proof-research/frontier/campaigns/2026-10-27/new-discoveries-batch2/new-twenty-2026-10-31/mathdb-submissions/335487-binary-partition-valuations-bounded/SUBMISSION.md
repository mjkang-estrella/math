# MathDB 335487: The 2-adic valuations of b_m(n) are bounded for infinitely many m not of the form 2^k − 1 (refutation of Gawron–Miska–Ulas Conjecture 5.3)

- Problem: https://mathdb.com/p/335487
- Source: Maciej Gawron, Piotr Miska and Maciej Ulas, “Arithmetic properties of coefficients of power series expansion of ∏_{n≥0}(1−x^{2^n})^t (with an Appendix by Andrzej Schinzel)”, arXiv:1703.01955 (2017); Monatsh. Math. 185 (2018); Conjecture 5.3. https://arxiv.org/abs/1703.01955
- Outcome: **REFUTED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `mathdb_335487_refuted`, `not_conjecture53`, `b11_not_dvd`, `family_not_dvd`, `family_counterexample`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The claim that carries weight is the infinite family; the single counterexample m = 11 is a routine fixed-exponent computation (a small scan plus a 70-state certificate modulo 32). Lean proves the bound ν₂(b_m(n)) ≤ 4 for the family and for m = 11; it does not assert that 4 is attained or classify the m with bounded valuations. Conjecture 5.3 concerns coefficients of negative powers (m-coloured binary partitions), not the positive-power sequences of the 2026 papers on the same product. No earlier resolution was found; the full texts of Ulas's IJNT 2019 paper and of one partition-polynomial paper were not readable (screened by abstract), and one omega registry query was rate-limited. Proof, first (same-model) review and Lean are by Claude Opus 5.5; the cross-model review and final check are by GPT-6.2 Sol (not routine 0.62).
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Refuted. Gawron, Miska and Ulas (arXiv:1703.01955, Conjecture 5.3) conjectured that the 2-adic valuation of b_m(n), the number of m-coloured binary partitions of n, is unbounded in n whenever m is not of the form 2^k − 1. For every m = 2^K(4^j + 1) − 1 with K ≥ 4 and j ≥ 1, and for m = 11, the valuation never exceeds 4. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $b_m(n)$ be the sequence considered in the paper and let $m\in\mathbb{N}_{\geq2}$ be such that $m$ is not of the form $2^k-1$ for any $k\in\mathbb{N}_{+}$. **Unbounded valuation conjecture.** The sequence

$$
\bigl(\nu_2(b_m(n))\bigr)_{n\in\mathbb{N}}
$$

is unbounded. This is proposed as a generalization of the preceding valuation observations, with the excluded values $m=2^k-1$ forming a separate family. The paper gives no general proof.

## Summary of the result

The conjecture is false, and not just at one value: for every m = 2^K(4^j + 1) − 1 with K ≥ 4 and j ≥ 1 (none of the form 2^k − 1), 32 never divides b_m(n), so ν₂(b_m(n)) ≤ 4 for all n; the same holds for m = 11. Here b_m(n) is the number of m-coloured binary partitions of n, the coefficient of x^n in the m-th power of the generating function of partitions into powers of 2. The proof reduces b_m(n) modulo 32 to a finite automaton reading the binary digits of n (from the Mahler functional equation (1 − x)H(x) = H(x²)), and handles all j at once by a second finite-state argument on pairs of digits of n and of the exponent, using a closed set of 31 polynomials. Lean defines binary partitions as partitions into powers of 2 (checked against the first values of OEIS A018819), proves the functional equation bridge, and checks the certificates in the kernel. Sobolewski and Ulas (Results Math. 2023) proved automaticity at each fixed modulus and stated that boundedness was not known for any admissible m.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
