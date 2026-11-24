# MathDB 322805: Congruence conjecture for signed power sums of Franel numbers

- Problem: https://mathdb.com/p/322805
- Source: Victor J. W. Guo, Proof of two conjectures of Sun on congruences for Franel numbers, arXiv:1201.0617, Conjecture 4.1 (Integral Transforms and Special Functions 24 (2013) 532-539). (https://arxiv.org/abs/1201.0617)
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `Franel.guo_conj_4_1`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Bounded literature search only, with one paper unread: Zhang and Yuan, Int. J. Number Theory 16(7) (2020) 1535-1546, 'Proof of three divisibilities of Franel numbers and binomial coefficients', is closed access. Its abstract says it confirms three conjectures of Guo and Zeng, and its only Guo-Zeng reference is their 2012 paper (arXiv:1008.2894), whose Conjectures 5.9(a), 5.9(b) and 5.10 fit; none of those is Guo's Conjecture 4.1 or implies it. One reviewer (GPT-6.1 Sol) left eligibility in doubt until that paper is read; the cross-model reviewer (Claude Opus) puts the risk that it covers this conjecture at about 2 percent. The journal text of the source is also unread. The tools are classical (the Guo-Zeng roots-of-unity method), so a specialist could call the proof a careful application of a known method (cross-model confidence: not routine 0.60; correct 0.97; Lean statement equals the printed conjecture 0.99).
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. For all n >= 1 and r >= 0, 2n divides sum_{k=0}^{n-1} (-1)^{rk} (3k+2) f_k^{(r)}, where f_k^{(r)} = sum_j C(k,j)^r. This is Conjecture 4.1 of V. J. W. Guo (arXiv:1201.0617), who proved r <= 3. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

For nonnegative integers $n$ and $r$, define

$$
f_{n}^{(r)}=\sum_{k=0}^n{n\choose k}^r.
$$

In particular, $f_n^{(3)}=f_n$ are the Franel numbers. **The signed Franel congruence conjecture.** Let $n\geq 1$ and $r\geq 0$ be two integers. Then

$$
\sum_{k=0}^{n-1}(-1)^{rk}(3k+2)f_{k}^{(r)}\equiv 0\pmod {2n}.
$$

This conjecture unifies the preceding congruences and Sun's fourth-power case; its status is not resolved in the supplied text.

## Summary of the result

For all integers n >= 1 and r >= 0, 2n divides the sum over k from 0 to n - 1 of (-1)^(rk) (3k + 2) f_k^(r), where f_k^(r) is the sum of the r-th powers of the binomial coefficients C(k, j). This is Conjecture 4.1 of Guo, who proved the cases r <= 3. The proof deforms the sum to a polynomial in q with Gaussian binomials, putting the weight q^(n-1-k)[k+j+1] on half of the sum, shows by the q-Lucas theorem and a block factorization with its phase signs that the deformation vanishes at every n-th root of unity other than 1, divides by the monic polynomial [n] over the integers, and sets q = 1; the factor 2 comes from the symmetry of the half-sum. Lean states the congruence in the integers exactly as printed, for every n >= 1 and every natural r.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
