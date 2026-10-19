# T242Z — single-fold Diophantine representations with integer unknowns

Status at freeze: unresolved research target. No proof, nominee or count claim.

Frozen UTC: 2026-10-19T03:00:22Z (recovery r4 of fresh-arithmetic-discovery-r72).

## Frozen full target

**T242Z.** For every integer n ≥ 1 and every recursively enumerable set
S ⊆ ℤ^n there are an integer m ≥ 1 and a polynomial
P ∈ ℤ[A_1,…,A_n,W_1,…,W_m] such that, for every a ∈ ℤ^n,

    #{ w ∈ ℤ^m : P(a,w) = 0 } = 1 if a ∈ S, and 0 if a ∉ S.

Quantifiers and strength: every n, every r.e. S, every integer input a
(including inputs with negative coordinates), and **all** m auxiliary
unknowns range over ℤ with no sign restriction. The count is over the
complete auxiliary tuple. Uniqueness is exact (single-fold), not
finite-fold, not "unique up to signs", and not restricted to inputs in S.
As in the source, the polynomial's coefficients may be established
non-effectively; no degree or unknown-count bound is part of the target.

The target contains the special case S = ℕ ⊆ ℤ, so it is equivalent to the
core statement (proved equivalent in `reduction-and-routes.md`, conditional
only on the stipulated source theorem):

**(N_ℤ).** There is Q ∈ ℤ[Z,Y_1,…,Y_k] with
#{ y ∈ ℤ^k : Q(z,y)=0 } = 1 for z ≥ 0 and = 0 for z < 0.

Neither the reduction nor any finite-fold, sign-normalized, restricted-input
or promise-only variant replaces T242Z. The integer promise corollary
("no algorithm decides integer solvability under an at-most-one integer
solution promise for fixed m, D") is a consequence of T242Z, not a substitute.

## Source dependency (stipulated true)

Source family 242, `preprints/Single-fold-Diophantine-representations-September-24-2026`,
pinned commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`:
`build/main.tex` Theorem `thm:main` (single-fold representation of every
r.e. S ⊆ ℕ^n with all unknowns in ℕ), Lemma `lem:composition`, and the
closing remark of `build/consequences.tex`: "The corollary makes no claim
about analogous uniqueness promises for solutions over ℤ or ℚ." The source
thus pays the entire ℕ-machinery; it does not pay positivity of unknowns.
Its arguments use nonnegativity of unknowns at the level of individual
operations, e.g. `build/power.tex` ("a nonnegative square root is unique")
and the sign codes z = z⁺ − z⁻ with z⁺,z⁻ ∈ ℕ in `build/main.tex` and
`build/elliptic.tex`.

## Chronology (honest)

Before this freeze, this recovery screened candidate families (see
`screening.md`) and made exploratory route calculations for (N_ℤ)
(Lagrange/Gauss selection, Pell positivity, greedy square-root recursion).
Those calculations are written up after the freeze in
`reduction-and-routes.md`; the freeze does not pretend to precede them.
No feasible full proof had been identified at freeze time; the feasibility
risk is explicit: the central difficulty, a single-fold positivity
certificate over ℤ, is entirely unpaid by the source.

Original prose: Myeongjin Kang, CC BY 4.0.
