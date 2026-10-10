# F006 — A convergent quartic reciprocal sum of degree 0′

Status: **proved normal-form corollary; independent review accepted after attribution corrections**. The noncomputable real is classical; its multiplicity-free quartic zero-set representation is the consequence studied here.

## Accepted upstream input

S1 is [Single-fold Diophantine representations, Theorem 1.1, `thm:main`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Single-fold-Diophantine-representations-September-24-2026/build/main.tex): every computably enumerable relation over N={0,1,…} has an integer-polynomial representation with exactly one complete auxiliary tuple for each member and none for nonmembers. Constants and coefficients are existential. Its [consequences section](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Single-fold-Diophantine-representations-September-24-2026/build/consequences.tex) does not state reciprocal-sum conclusions.

**Statement.** There exists a fixed quartic `R(N,Z)` of the same nonnegative sum-of-squares form, with at most one natural witness per `n`, no zero at `n=0`, and infinitely many zeros, for which

`θ = Σ_{(n,z):R(n,z)=0}1/n`

is finite, left-c.e., transcendental, and has Turing degree exactly `0′`.

**Convention.** The Turing degree of a real is the degree of its rational Dedekind cut. For the irrational θ obtained below this agrees with the digit-expansion and computable-approximation conventions used by the proof. A cut oracle gives arbitrarily accurate approximations by bisection. Once noncomputability establishes irrationality, approximations also decide each rational cut query.

**Proof.** Let `K` be an infinite c.e. halting set of degree `0′`, and apply S1 to
`A={4^{e+1}: e∈K}`. Apply the [uniqueness-preserving natural circuit conversion proved in F005](F005-quartic-sum-convergence.md): split positive and negative coefficients, introduce deterministic nonnegative addition/multiplication gates, and sum squares of all gate residuals. Then

`θ=Σ_{e∈K}4^{-e-1} ≤ 1/3`.

Enumerating zero tuples gives an increasing computable rational approximation, so `θ` is left-c.e. A `K` oracle computes the first `L` membership bits; the omitted tail is at most `4^{-L}/3`, so `θ≤_T K`.

Conversely recover membership inductively. Having subtracted all recovered earlier digits, set `w=4^{-e-1}`. If `e∉K`, the residual is at most `w/3`; if `e∈K`, it is at least `w`. Approximation with error below `w/12` distinguishes these cases by the threshold `2w/3`. Thus `K≤_T θ`. This separated-digit argument avoids binary carry ambiguity. Therefore `θ` is noncomputable. Every real algebraic number is computable, by isolating its root with rational intervals and effective bisection, so `θ` is transcendental. ∎

This also excludes a computable modulus of convergence for any computable monotone zero-tuple enumeration of this sum: such a modulus would compute `θ`. The elementary geometric tail in the **digit index** is not a modulus in zero-tuple enumeration order; discovering the corresponding witnesses requires halting information.

**Novelty caution.** The real Σ_(e∈K)4^(−e−1) is a classical Specker-type real; see [Specker (1949), *Nicht konstruktiv beweisbare Sätze der Analysis*](https://doi.org/10.2307/2267043). Noncomputable sums and arithmetic encodings of halting information are classical. [Chaitin, *Incompleteness theorems for random reals* (1987)](https://doi.org/10.1016/0196-8858(87)90010-8) uses exponential Diophantine solution-count encodings. [Ord–Kieu (2003)](https://arxiv.org/abs/math/0301274) gives further Ω encodings involving exponential equations and polynomial value sets. The feature here is direct, multiplicity-free summation over zeros of one ordinary nonnegative quartic. No randomness claim is made for `θ`; degree `0′` does not imply Martin-Löf randomness.

## Effectivity and validation

As in F005, a fixed ordinary polynomial exists, but this research does not
supply its numerical coefficients or dimension. No exponential-polynomial
encoding is substituted silently. Naturals, including all gate variables,
are the domain; uniqueness over integers or rationals is not asserted.

[Independent review](../reviews/diophantine_sums-r1.md), theorem 2, accepted
the proof after specifying the real-degree convention and Specker prior
work, both incorporated here. The parent independently checked the
1/3 tail bound, the gap between w/3 and w and threshold 2w/3, and why a
computable enumeration modulus would compute θ. Exact base-four gap
checks passed in `experiments/independent_scout.py`. No proof-assistant
verification is claimed.
