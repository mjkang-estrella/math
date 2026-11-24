# MathDB 338558: The generic-rank conjecture for bipartite circulant graphs

- Problem: https://mathdb.com/p/338558
- Source: Daniel Irving Bernstein, Grigoriy Blekherman and Rainer Sinn, Typical and Generic Ranks in Matrix Completion, arXiv:1802.09513, Conjecture 5.6 (Linear Algebra and its Applications, 2020). (https://arxiv.org/abs/1802.09513)
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `Circulant.mathdb338558`, `Circulant.literalConjecture_proved`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Bounded literature search only. Cross-model confidence: correct 0.98, not public 0.85, not routine 0.75, Lean statement equals the printed conjecture 0.97. The printed formula omits a ceiling; the Lean formula n - Nat.sqrt(n(n - l)) equals the dimension-count prediction the conjecture names (checked for n <= 12). Closest later work: Dressler and Krone, arXiv:2010.09777, on real typical ranks of the same graphs, which does not prove the complex formula.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Every bipartite circulant graph G(n, l) has generic completion rank n - floor(sqrt(n(n - l))), as predicted by the dimension count. This is Conjecture 5.6 of Bernstein, Blekherman and Sinn (arXiv:1802.09513), which the source proves only for special families. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $G(n,l)$ be a bipartite circulant graph of the form considered in the paper, and let the generic completion rank be the rank attained by a generic matrix completion. The dimension-count prediction is

$$
n-
\left\lfloor\sqrt{n^2-nl}\right\rfloor.
$$

**Bipartite circulant generic-rank conjecture.** Every graph $G(n,l)$ has generic completion rank predicted by the dimension count; equivalently,

$$
\operatorname{gcr}(G(n,l))=n-\left\lfloor\sqrt{n^2-nl}\right\rfloor.
$$

The paper proves the dimension-count prediction for a subset of these graphs and conjectures it for all bipartite circulant graphs of this form. The claim is presented as unresolved.

## Summary of the result

For all n > 0 and 0 <= l <= n, the bipartite circulant graph G(n, l) has generic completion rank n - floor(sqrt(n(n - l))), the value predicted by the dimension count. This is Conjecture 5.6 of Bernstein, Blekherman and Sinn, who proved it for special families and named the step that was missing. The upper bound uses a new construction: Fourier vectors with an evenly spaced (Beatty) set of frequencies, so that each frequency class has at most d elements, and a Vandermonde system on the missing diagonals that forces the tangent map to be injective. The lower bound is the dimension count. Lean states generic completion rank literally, as a statement about a nonempty Zariski-open set of partial matrices in both directions, and proves the passage from a nonzero Jacobian minor to such an open set.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
