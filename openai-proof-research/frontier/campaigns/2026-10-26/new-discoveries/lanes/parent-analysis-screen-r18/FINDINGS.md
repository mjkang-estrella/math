# Analysis screen r18 — no new credit

## MathDB 372380: prior public resolution found before formal investment

Henry's arXiv:2601.00631v1, Conjecture 1 (printed p.7), is exactly the
two-sided inequality in the saved live MathDB record. Reflection reduces
it to x < F(x) < (gamma+1/2)x+gamma-1/2, where
F(x)=zeta(x)-psi(1-x), 0<x<1. Root read the actual source PDF text.

The initial root reasoning independently suggested convexity for the upper
bound and a rational polynomial certificate for the small positive lower
margin. Numerical checks support it; none constitutes a proof or credit.

Mandatory early prior-art search found Gao–Guo arXiv:2601.09276v1,
submitted 14 January 2026. The actual downloaded body explicitly states
**Corollary 1.3**, the entire identical pair of inequalities, and says this
implies Henry's Conjecture 1.1 (= source Conjecture 1). Theorem 1.2 states
strict convexity, monotonicity, and endpoint derivatives for this exact F.
The parent read these statements and the proof's concluding paragraph.

Publication also exists as Liwen Gao, *Inequalities for zeta(s)-psi(1-s)
Related to a Conjecture of Henry*, Axioms 15(8),577 (2026),
DOI 10.3390/axioms15080577. The publisher body was blocked (429), so only
the actual arXiv body is relied on here; no claim of byte-identical
published mathematics is made.

The arXiv lower-bound proof uses a Mathematica computation of the unique
minimum, approximately 0.00306469, without an explicit interval certificate
in that paragraph. This is an accuracy limitation of the posted proof, not
permission to claim the already publicly stated identical resolution as a
new discovery. Root did not audit the full predecessor proof. A later
formal or certified repair would remain uncredited under the campaign rule.

**Decision: no discovery credit, no Lean/manuscript investment.** MathDB's
open/empty label does not outweigh the explicit prior public resolution.
No external communication. Saved sources and fresh live records remain
under `sources/`. Other queried records are leads only, not resolved here.

Primary links:
- https://arxiv.org/abs/2601.00631
- https://arxiv.org/abs/2601.09276
- https://doi.org/10.3390/axioms15080577

## MathDB 345844: immediate source-facts counterexample, excluded from credit

Root read the actual latest arXiv:2003.06025 body, Conjecture 1 (printed p.14),
Lemma 4.1 (p.14), Proposition 4.2 (p.15), and Corollary 3.9 (p.13).
Let M be the geometric mean G_{0,0} and lambda_n=2^n (n>=1).
Then lambda_n/Lambda_n=2^n/(2^{n+1}-2) decreases to 1/2; Lambda_n diverges.
Lemma 4.1 gives H_M(lambda)=(1-1/2)^(1-2)=2.
For each k, set psi^(k)_n=2^n for n<=k and psi^(k)_n=1 for n>k.
These positive weights converge pointwise to lambda. For each k their total
weight diverges and psi^(k)_n/sum_{j<=n}psi^(k)_j tends to zero.
Proposition 4.2 gives H_M(psi^(k))=e for every k. The geometric mean is
symmetric, monotone, continuous in its weights, and 1-Hardy (same lemma with
unit weights gives H_M(1)=e). Thus the conjectured continuity is false.

This is an immediate combination of the SAME source's two explicit formulas,
using eventual constant tails. It fails the campaign's substantive standard;
no count, no claim of a new-to-literature theorem, no Lean/paper investment.
The direct local registry search found no relevant entry, but this cannot
turn an immediate source-facts corollary into discovery credit.
