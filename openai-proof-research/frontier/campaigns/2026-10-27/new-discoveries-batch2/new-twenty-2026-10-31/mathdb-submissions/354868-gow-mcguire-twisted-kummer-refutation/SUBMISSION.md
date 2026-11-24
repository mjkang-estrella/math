# MathDB 354868: Injectivity conjecture for evaluation maps of linearized polynomials

- Problem: https://mathdb.com/p/354868
- Source: Rod Gow and Gary McGuire, Linearized Polynomials, Galois Groups and Symmetric Power Modules, arXiv:2206.01551 (2022), Conjecture 1. (https://arxiv.org/abs/2206.01551)
- Outcome: **REFUTED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `Gow.mathdb_354868_false`, `Gow.concrete_counterexample`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Bounded literature search only; the source exists only as an arXiv preprint (no journal version found). The Lean statement of the conjecture is its specialization to q = p = 3, with all hypotheses of the source; refuting that special case refutes the conjecture. Cross-model confidence: correct 0.98, not public 0.85, not routine 0.65, Lean statement 0.97; overall about 0.6 that a specialist accepts it as more than an exercise, the risk being that additive twisting looks natural once suggested. A plain search would not find it: finite base fields are covered by the source's Theorem 12 and the mechanism needs n >= 4. Whether the conjecture fails for n = 3 is not settled.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Refuted. For q = 3, n = 4, r = 2 the 3-polynomial L = X^81 + (t+t^2)X^27 - (t+t^2)X^9 + (t+t^2)X^3 - t(t^2+t+1)X over F_3(t) satisfies every hypothesis of Conjecture 1 of Gow and McGuire (arXiv:2206.01551), and the map epsilon_2 is not injective. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $L=L(x)$ be a $q$-polynomial in $F[x]$ of $q$-degree $n$, where $F$ is a field of characteristic $p$ that contains $\operatorname{\mathbb{F}}_q$. Assume that $L$ is not a $q^s$-polynomial for $s>1$, and that $L(x)/x$ is irreducible over $F$.

**Injectivity conjecture.** If $1\le r\le q-1$, then the evaluation map $\epsilon_r$ is injective.

This conjecture predicts injectivity in the range $1\le r\le q-1$ under irreducibility and a non-$q^s$-polynomial hypothesis. The surrounding results establish related injectivity statements for evaluation maps, but the supplied text does not state whether this conjecture has been resolved.

## Summary of the result

Conjecture 1 of Gow and McGuire is false. Over F = F_3(t) the 3-polynomial L = X^81 + (t + t^2) X^27 - (t + t^2) X^9 + (t + t^2) X^3 - t (t^2 + t + 1) X has 3-degree 4, L/X is irreducible over F, L is not a 3^s-polynomial for any s > 1, and r = 2 <= q - 1, yet the evaluation map epsilon_2 on quadratic forms in a basis of the root space is not injective: an explicit seven-term quadratic form vanishes on the roots (the image has dimension 8 in a space of dimension 10). The roots are the image of u F_81, with u^80 = t, under the additive twist x -> x + x^3 of the Kummer polynomial X^81 - tX; the twist keeps irreducibility, because the automorphisms u -> cu act transitively on the nonzero roots, and it forces the kernel. Lean states the conjecture for q = p = 3 with every hypothesis of the source and proves its negation with this witness, including irreducibility and the splitting field.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
