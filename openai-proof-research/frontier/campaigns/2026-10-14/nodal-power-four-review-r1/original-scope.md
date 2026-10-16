# Frozen original scope: fresh analytic discovery r13

Author: Myeongjin Kang (no affiliation). Original prose CC BY 4.0.

Pinned upstream: openai/math `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`,
accepted as true. Source family 350 (Yau's nodal bounds: surfaces and
higher dimensions). This family is distinct from every target family of
the 2026-10-14 campaign recorded in the brief (Brenier/log-concavity,
Salem/Bernoulli convolutions, Coulomb, EPnI, strict BV, FK, Artin,
torsion-free solutions, spin Q4, relative CI, unimodality, Hamiltonian
span, and the accepted p-gradient, matrix-disk, kinetic and staircase
results).

## Target T4 (frozen before sustained proof work)

**T4.** There exist a smooth Riemannian metric g on the closed connected
four-manifold S^3 x S^1, a number epsilon_0 > 0, and nonzero real smooth
functions u_j on S^3 x S^1 with positive numbers lambda_j such that

    -Delta_g u_j = lambda_j u_j,     lambda_j -> infinity,
    H^3_g(Z(u_j)) / lambda_j^(1/2 + epsilon_0) -> infinity,

where Z(u) is the zero set and H^3_g is three-dimensional Hausdorff
measure of the Riemannian distance. The metric and epsilon_0 are fixed
along the sequence.

Equivalently: the smooth upper-bound assertion of Yau's nodal conjecture
fails in dimension four even with an arbitrarily small positive power
loss. The pinned sources prove this failure only in dimensions at least
five (`Power-law-violations-of-Yaus-nodal-upper-bound`, Theorem 1.1 and
its product remark) and state explicitly that they make no assertion in
dimensions three or four. The companion dimension 3/4 paper proves only
unbounded normalized nodal measure (no fixed power).

Out of scope, and not to be substituted on failure: dimension three,
qualitative (non-power) unboundedness, weighted operators that are not
Laplace-Beltrami operators, metrics that vary with j, and any smaller
statement (for example, only the envelope lemma) presented as T4.

## Operation-level screen performed before freezing

After the standard transformations (products with a fixed manifold,
warped-circle realization of weighted operators, rescaling, changes of
finite accuracy order), the unpaid nonroutine operation is the
**quantitative repeatable envelope amplification in base dimension three**.
The pinned power-law paper uses base dimension four exactly once, in its
corrugation lemma (envelopes.tex: "This is where base dimension four is
used: in dimension d the corresponding intersection lower bound is
d-3"). The dimension 3/4 paper's three-dimensional amplification
(s3-profiles.tex, Proposition prop:profile-amplification) is
qualitative: its patch sizes and thresholds depend on the entire incoming
profile, so it gives no derivative control and no fixed power. Products,
warping, and parameter changes do not supply this step.

Success requires a complete proof of T4 or a genuine counterexample-type
obstruction to T4 itself (not merely to one construction route).
