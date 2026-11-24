# MathDB 340107: Submultiplicativity conjecture for the primitive-set ratio function

- Problem: https://mathdb.com/p/340107
- Source: Nathan McNew, “Counting primitive subsets and other statistics of the divisor graph of {1,...,n}”, arXiv:1808.04923 (2018). (https://arxiv.org/abs/1808.04923), Conjecture 1
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `PrimitiveRatio.mcnew_conj1`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Modest: about a page using a correlation inequality; a specialist in correlation inequalities might find it quickly, but it is not a corollary of a published theorem. Bounded literature search only. The prior-work paragraph of the paper still refers to internal review files and should be tidied before external use.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. With Q(k) the number of primitive subsets of {1,...,k} and g(k) = Q(k)/Q(k-1) - 1 (g(1) = 1), g(nm) <= g(n) g(m) for coprime n and m, and g(p^(i+1)) <= g(p^i) for every prime p. This is Conjecture 1 of McNew, arXiv:1808.04923. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

For $k>1$, let $Q(k)$ be the number of primitive subsets of $\\{1,2,\ldots,k\\}$ and define

$$
g(1)=1,\qquad g(k)=\frac{Q(k)}{Q(k-1)}-1.
$$

Thus $g(k)$ is the ratio of primitive subsets of $\\{1,2,\ldots,k\\}$ that contain $k$ to those that do not. **Submultiplicativity conjecture for $g$.** The function $g$ is submultiplicative in the following sense: if $(n,m)=1$, then

$$
g(nm)\leq g(n)g(m),
$$

and, for every prime $p$,

$$
g(p^{i+1})\leq g(p^i).
$$

These inequalities are proposed as conjectural improved upper-bound tools for the exponential growth constant associated with counting primitive sets. The supplied text gives no resolution of this conjecture.

## Summary of the result

Let Q(k) be the number of primitive subsets of {1,...,k} (no element divides another; the empty set is counted, as in OEIS A051026) and g(k) = Q(k)/Q(k-1) - 1, with g(1) = 1. Then g(nm) <= g(n) g(m) for coprime n, m >= 1, and g(p^(i+1)) <= g(p^i) for every prime p and i >= 0. This is McNew's Conjecture 1. The proof uses an antichain-avoidance monotonicity lemma (an FKG-type correlation inequality) and two block reductions.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
