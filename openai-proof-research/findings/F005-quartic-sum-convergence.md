# F005 — Σ₂⁰-complete convergence with infinitely many unique-fiber zeros

Status: **proved normal-form corollary; independent review accepted after attribution corrections**. This is a routine combination of single-fold representation and classical computability. No literature-priority claim.

## Accepted upstream input

S1 is [Single-fold Diophantine representations, Theorem 1.1, `thm:main`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Single-fold-Diophantine-representations-September-24-2026/build/main.tex): every computably enumerable relation over N={0,1,…} has an integer-polynomial representation with exactly one complete auxiliary tuple for each member and none for nonmembers. Constants and coefficients are existential. Its [consequences section](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Single-fold-Diophantine-representations-September-24-2026/build/consequences.tex) does not state reciprocal-sum conclusions.

**Statement.** There exist a fixed integer `m` and a fixed polynomial `Q(E,N,Z₁,…,Z_m)` of total degree at most four, presented as a sum of squares of integral polynomials of degree at most two, such that for every `e∈N`:

1. for each `n`, at most one `z∈N^m` solves `Q(e,n,z)=0`, and no solution has `n=0`;
2. there are infinitely many pairs `(n,z)` solving it;
3. the index set
   `C={e : Σ_{(n,z): Q(e,n,z)=0} 1/n < ∞}`
   is Σ₂⁰-complete under computable many-one reductions.

In particular neither convergence nor divergence is semidecidable on this fixed, entirely promised family. Summation is over **all zero tuples**, without existential projection or deduplication; uniqueness makes it equal to the sum over allowed `n`.

**Proof.** Let `W_e` be a standard uniformly c.e. family, and define the uniformly c.e. relation

`A_e = {2^k : k≥0} ∪ ⋃_{0≤j<|W_e|} [4^j, 2·4^j−1]`.

The interpretation is: enumerate block `j` once `j+1` distinct members have appeared in `W_e`. The relation `(e,n): n∈A_e` is c.e., even though its cardinality condition is not generally decidable. All `A_e` are infinite and exclude zero.

If `W_e` is finite, only finitely many blocks are added, and the powers of two contribute `Σ_k 2^{-k}=2`; hence `Σ_{n∈A_e}1/n` converges. If `W_e` is infinite, every block occurs. Blocks are pairwise disjoint and each has `4^j` terms, all at most `2·4^j`, so each contributes at least `1/2`. Hence the sum diverges. Overlaps with the powers of two cause no trouble: the disjoint blocks alone supply the divergent lower bound.

S1 gives a fixed polynomial `P(e,n,w)` whose entire natural witness tuple is unique exactly for this relation. Apply the classical Skolem/Davis arithmetic-circuit degree reduction (also used with unique extension in the upstream H10(Q) corollary `thm:degree-normal-form`) over N, retaining uniqueness: write `P=P₊−P₋` with both parts having nonnegative integer coefficients. Evaluate each part by a fixed acyclic addition/multiplication circuit. Introduce a natural variable for every gate, enforce `u=c`, `u=v+w`, or `u=vw`, and equate the two output gates. For fixed inputs `(e,n,w)`, induction through the circuit gives one and only one natural assignment to its gate variables. Squaring and adding every gate residual and the output equality yields `Q`; each residual has degree at most two, and the complete zero tuple consists of `w` and every gate. This proves all structural assertions. Splitting signed coefficients is necessary: direct evaluation of a signed circuit could force a negative natural gate.

For the upper complexity bound, enumerate all zero tuples in expanding finite boxes. Their finite partial reciprocal sums `s(e,t)` are uniformly computable rationals, monotone in `t`, with supremum equal to the full sum. Thus convergence is precisely `∃B∈N ∀t [s(e,t)≤B]`, a Σ₂⁰ predicate. For hardness, `e∈C` iff `W_e` is finite. Here is a direct proof that FIN is Σ₂⁰-complete: given any predicate `∃b∀t R(e,b,t)` with computable `R`, at stage `s` let `b_s` be the least `b≤s` satisfying all tests `t≤s`, or `s+1` if none; enumerate the initial segment `{0,…,b_s}`. A true witness makes `b_s` eventually bounded, producing a finite set. Without a witness, every fixed candidate is eventually excluded, so `b_s→∞`, producing an infinite set. The s-m-n theorem turns this uniform enumeration program into a computable map from e to its enumeration index, completing the many-one reduction. ∎

**Effectivity boundary.** S1 supplies existence, not numerical coefficients or an algorithm choosing its arithmetic constants. After choosing one fixed `P`, its finite code can be hard-coded, and all specializations are computable. Accordingly the theorem is existential about a fixed family; this session does not produce a usable explicit universal quartic. Fixed dimension, fixed degree, and fixed number of summands are justified, but their numerical values are not.

## Novelty boundary and validation

Σ₂-completeness of reciprocal convergence over arbitrary c.e. sets is
classical. Diophantine **projected value sets**, with duplicate witnesses
removed, were already available from DPRM. The new input permits direct
summation over **all complete zero tuples**, with no projection or
deduplication, while keeping one fixed nonnegative degree-at-most-four
polynomial and infinitely many zeros on every input. The circuit reduction
and FIN argument are not new mechanisms.

[Independent review](../reviews/diophantine_sums-r1.md), theorem 1, accepted
the proof after the three attribution/effectivity clarifications now made.
The parent independently checked the two-case FIN reduction, uniqueness of
all natural gate values, and the Σ₂ upper bound.

`python openai-proof-research/experiments/independent_scout.py` passed exact
block-mass, separated-digit and natural-gate checks. Its prime-factor sieve
is unrelated to this result. These finite checks do not construct the
existential universal polynomial or prove completeness. No proof-assistant
verification is claimed.
