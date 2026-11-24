# MathDB 366504: The derivation construction for transposed Poisson n-Lie algebras fails at n = 3

- Problem: https://mathdb.com/p/366504
- Source: Farukh Mashurov, “On the transposed Poisson n-Lie algebras”, arXiv:2501.01714 (2025); Comm. Algebra (2026), doi 10.1080/00927872.2026.2689550; Conjecture 1.1. https://arxiv.org/abs/2501.01714
- Outcome: **REFUTED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `TP366504.not_derivationConstructionConjecture`, `TP366504.mathdb366504_rat`, `TP366504.mathdb366504_complex`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The signed universal conjecture fails at n = 3; the Lean theorem covers fields of characteristic 0 (including ℚ and ℂ). The restriction to a 59-dimensional example and the extension to positive characteristic other than two are written arguments outside Lean. The witness is nonunital and infinite-dimensional (the conjecture requires neither); the result does not settle the unital case or other arities. The unsigned printing of the formula fails trivially and is not a separate result. The journal version (Comm. Algebra, doi 10.1080/00927872.2026.2689550) could not be read; arXiv v3 predates its acceptance, and the November 2026 version of the Beites–Ferreira–Kaygorodov survey still lists the question as open. Proof, first (same-model) review and Lean are by Claude Opus 5.5; the cross-model review and final check are by GPT-6.2 Sol (two rounds; not routine 0.67).
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Refuted. Mashurov (arXiv:2501.01714) conjectured that a derivation D of a transposed Poisson n-Lie algebra yields a transposed Poisson (n+1)-Lie algebra through the signed sum of D(a_i)[a_1, …, â_i, …, a_{n+1}]. This fails at n = 3 over every field of characteristic 0: for an explicit algebra over the polynomial ring K[t] with D = d/dt, the resulting 4-ary operation violates the Filippov identity. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $n\geq 2$ be an integer. Let $(L,\cdot,[\cdot,\ldots,\cdot])$ be a **transposed Poisson $n$-Lie algebra**, and let $D$ be a derivation of both $(L,\cdot)$ and $(L,[\cdot,\ldots,\cdot])$. Define an $(n+1)$-ary operation

$$
\mu(a_1,\ldots,a_{n+1})=\sum_{i=1}^{n+1}(-1)^{i-1}D(a_i)[a_1,\ldots,\hat{a}_i,\ldots,a_{n+1}],
$$

where $\hat{a}_i$ denotes omission of the $i$-th entry. **Derivation construction conjecture.** Then $(L,\cdot,\mu(\cdot,\ldots,\cdot))$ is a transposed Poisson $(n+1)$-Lie algebra. This conjecture extends the known construction for transposed Poisson 2-Lie algebras and addresses the open question of constructing and classifying simple transposed Poisson $n$-Lie algebras. Its validity for arbitrary $n\geq 2$ and the stated derivations remains open.

## Summary of the result

The conjecture is false at n = 3 over every field of characteristic 0. The counterexample is a transposed Poisson 3-Lie algebra M₃ given by an explicit multiplication and bracket table, extended to polynomials in one variable t, with the derivation D = d/dt; the 4-ary operation μ built from D and the bracket fails the generalized Jacobi (Filippov) identity, with an explicit nonzero defect. The idea is that D = d/dt on the polynomial extension turns the Filippov defect of μ into a polynomial identity (a 'strong condition' whose first argument is itself a bracket) that would have to hold in the base algebra, and the table is chosen so that this degree-seven specialization is nonzero. Huang, Chen, Chen and Ding proved the construction for strong transposed Poisson n-Lie algebras, and Mashurov showed by a free-algebra computation that the strong condition can fail, without producing a counterexample to the construction. Lean states the conjecture with the bracket as a function with multilinearity and skew-symmetry hypotheses, over any field of characteristic 0, and proves its negation.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
