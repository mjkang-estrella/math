# H023 — Coordinator disposition

2026-10-08. **ACCEPT the finite geometry counterexample and primitive candidate
population. ACCEPT the displayed optimizations as conditional real models.
Close promotion of this construction to a new factoring algorithm.**
Verified full factoring complexity improvement: **NONE**.

## Review and provenance

The coordinator read all 625 lines of the [independent review](H023-independent-review.md).
It accepted the complete 661-line proposer report and parent I1–I4 without
mathematical corrections. Its only requested revision was to include
Kleinjung section 6.7 in the rotation citation; that change is applied.

The [submitted report](H023-submitted-draft.md) is preserved byte-for-byte:
`c025d0e2c52ad9deb9540a8514cd170c2779e18e02cd60838b65a65b1974eeb3`.
The [submitted parent intake](H023-intake-submitted.md) is also preserved:
`1fcb6070d9bf16c8a961054d2fad83c8f2123543caf8782c5170744d4bc62618`.
Review SHA256:
`8b15c73f8d47569881ab105238b5f93e11f7fb870754e297cb6fd271c49da23c`.
All three original hashes matched at intake.

## Accepted finite and asymptotic mathematics

For even d>=4, even m>=2^(d+7), and independent odd
M in [m/2^(d+3),m/2^(d+2)], the polynomial

    f(X)=(X+1)^(d-2)(X²+M+1)+1

is exactly the ordinary-base polynomial of N=f(m), with
m=floor(N^(1/d)), odd N, and actual gamma=1 at the stated degree scale.
Its family has an N-only polynomial-time recognizer, not an all-input selector.

Two strict Rouche counts for f(Y-1) put d-2 roots near Y=0 and a nonreal
conjugate pair outside the unit disk. The integer constant-term argument
proves irreducibility before invoking characteristic-zero square-freeness.
Every eligible H020 complement retains the cluster. Its true normalized
separation has log(1/kappa)>=(delta^(-2)+o(1))D, so no better certificate can
make the required o(D) premise hold for this ordinary-base family.
An alternative polynomial representation of the same N may differ.

Positive primitive rectangles supply an attained candidate population,
paid raw enumeration, exact positive norms and a uniform edge norm stratum.
At the exact Q_threshold=1 cutoff and a delta²=2, their exponent is 3a/2;
the geometry-free H022 formula would give only a. This disproves deletion
of that hypothesis, without changing the accepted conditional H022 theorem.

The fixed-degree family count is Theta(2^(-d)T^(2/d)) in the stated uniform
range T^(1/d)>>2^(d+7). The usual-scale compact-degree union is sparse,
exp(O(V)) up to exp(t). This bound is not for the entire all-degrees
recognizer: fixed d=4 already gives Theta(T^(1/2)) members. Easy composite
subsequences disprove uniform geometry within the composite promise, but no
balanced-semiprime or hard-family density follows.

## Conditional models and matched baselines

The original anisotropic rectangle has exact relaxed infimum C³=16/3.
The degree-halved alternative has the reviewed identities, irreducibility
and actual coefficient sizes; its positive even-degree skewed model gives
40/9. Different optimizing delta values do not prove fixed-input dominance.

The parent binomial subfamily M=1 mod4 and (d-2)/s even gives an Eisenstein
polynomial, a genuine common modular root and correct rational denominator
numerator. For each fixed s>=1 the displayed real optimization is

    C_s³=32(s+1)/(9s).

These model values approach 32/9 across different fixed-s optimized families.
They are not a uniform growing-s factoring theorem, and the restrictions and
degree scale must hold on a given input. Equal constants at s=4 and in the
degree-halved comparison do not identify the subfamilies.

Primary sources support classifying these mechanisms as special-form NFS
with skewed regions, translation and rotation. No exhaustive optimal-baseline
or priority claim is made. The computations do not establish a new factoring
record merely by improving an isotropic generic calculation.

## Remaining obligations and next action

Candidate population does not imply usable doubly smooth supply. Bad-prime
exclusion, ideal/character information, rank, unit/class obstructions,
square-root reconstruction and denominators, proper gcd probability and
restarts remain unpaid or unproved as full algorithmic guarantees.
The compatible H016 processing costs do not resolve these issues.

Retain the geometry counterexample and close this proposed new-algorithm
claim. Reopen only for a specific new primitive or a post-filter useful-yield/
extraction claim that survives comparison on the same inputs and available
representations. No finite experiment is warranted merely to test the
symbolic identities or novelty.

H026's separate low-energy lattice supply argument is under review. No
implementation, experiment, package or Lean change was made for H023.
Prior shared checks remain the latest checks; no document-only rerun occurred.
