# H043 conjugate-point prices do not supply a complete search

2026-10-09 UTC. Raw Grok4.7 report and retained task ID are in
H043-fullwork-grok-raw.md. No new labelled successor, solver or experiment was
submitted. Root checked primary formulas; native Sol reviewed arithmetic,
collision counting and detection costs. No executable run, benchmark or H034
cap reset. Verified improvement NONE; working exponent1/2 unchanged.

## What the arithmetic comparison actually prices

For nonexceptional affine inputs W,J with distinct abscissae, a shared inverse
of x(J)-x(W) gives one full sum using I+2M+S. Computing the opposite sum with
the same denominator takes a further2M+S; its abscissa alone takes M+S.
These counts follow directly by forming the two slopes, their squares and
the required ordinates in [EFD's affine formulas](https://www.hyperelliptic.org/EFD/g1p/auto-shortw.html).
Infinity, equal-abscissa and doubling branches must be dispatched separately.

For a batch of K nonzero denominators, the standard prefix/backward inverse
schedule costs I+3(K-1)M, not an identity I=3M. Thus define
epsilon_K=(I-3M)/K in the arithmetic ledger. The particular schedules cost

    one full sum                    5M+S+epsilon_K,
    two full conjugate points       7M+2S+epsilon_K,
    one full sum and side abscissa   6M+2S+epsilon_K.
    both abscissae only              5M+2S+epsilon_K.

They omit additions, representation/label work, memory traffic, exceptional
branches, detection, recovery and verification. When epsilon_K is neglected,
the two mixed/full pair prices per emitted key are3.5M+S and3M+S. Relative to the
recorded2.5M+S x-only key schedule, these particular key-generation prices
are higher. A complete-solver comparison additionally needs the SAME useful
coverage/collision and detection model; price per key alone is not a proof
of whole-solver dominance. Square/multiply ratios here are assumptions, not
hardware measurements. The earlier approximately0.19sqrt(q) memory crossing
was a conditional field-only comparison, not a universal low-memory boundary.
The both-abscissae row has2.5M+S per key in the same limit, but omits the
ordinate required by this ordinary full-point walk update. A key generator
and a propagated walk state are distinct operations with different invoices.

Root also read the author-hosted [co-Z paper, section4 and Table1](https://marcjoye.github.io/papers/GJMRV11regpm.pdf).
ZADDC gives two conjugate projective outputs at6M+3S from inputs that already
share Z, incrementally M+S above its co-Z update. The paper also gives an
(X,Y)-only variant at5M+3S under a different state/recovery schedule. Neither
invoice automatically applies to an arbitrary hash-selected jump; maintaining
the shared-coordinate invariant and extracting comparison keys must be priced.
The scalar ladder in the paper does not by itself specify a collision walk.
This is not a proof that every shared-coordinate search is impossible.

[EFD's dadd-2002-it-3 entry](https://www.hyperelliptic.org/EFD/g1p/auto-shortw-xz.html#diffadd-dadd-2002-it-3)
lists7M+2S PLUS multiplication by each curve parameter, four additions and a
small-constant operation. It requires the difference point. Parameter operations
were omitted from the raw abbreviated comparison; specialized curves may
price them differently. These are projective outputs, whose normalization or
projective equality protocol also costs work. A different maintained-difference
schedule would need its own label, state and useful-collision analysis.

## Correcting the extra-sample collision model

The raw (1+c)/sqrt(2) ratio does not follow from its stated ideal of two
independent always-detected outputs per round. In a uniform IID model on N
keys, with EVERY unordered pair detected, n rounds produce2n samples.
The leading birthday stopping round count is therefore half the one-output
count, and the arithmetic ratio is (1+c)/2. A sqrt(2) factor would require
a separately specified eligible-pair model, not merely two emitted samples.
This correction is an ideal counting calculation, not a prediction for the
actual correlated conjugate outputs or a low-memory improvement claim.

Actual side points are functions of the main point and jump. They need not
follow an independent distribution, and a side collision does not make two
main walk trajectories coalesce automatically. A detector must state which
main/side pairs it sees, their dependence, useful label differences, storage,
false positives, replay, nulls and restarts. Retaining every side point is one
possible design, not a proved necessity: distinguished points, sparse filters,
replay or other paid schemes can be analyzed if concretely supplied. No such
complete new scheme was specified here. Consequently the raw claim that all
three schedules provably lose at complete cost is withdrawn; no gain has
been demonstrated either.

For ordinary point or abscissa collisions, labels still must yield a nonzero
coefficient of the unknown scalar after any sign choice. Zero-coefficient
relations and repeated samples are not successful recovery events. A uniform
birthday law does not automatically count only useful collisions.

## The proposed sum feature is degree two, not three

Write f(t)=t^3+a_E*t+b_E and J=(a,y_J), with f(a)!=0. Addition formulas give

    x(W+J)+x(W-J)
      =2*(a*t^2+(a^2+a_E)*t+a_E*a+2b_E)/(t-a)^2,
    t=x(W).

The cubic terms cancel. At t=a the numerator is4f(a)!=0, so this is a
degree-two rational map. Its equality remains a feature collision, not an
automatic equality of labelled curve points. Inverting the small feature
fiber recovers possible abscissae, not necessarily a scalar relation. A
specific recovery map could change that assessment; none was supplied.
The degree itself proves no general cost or information lower bound.

## Remaining scope and sources

The0.886sqrt(q) negation-rho iteration constant remains the previously scoped
heuristic reference, not a proved full runtime. Fresh browser access to the
Bernstein–Lange–Schwabe PDF failed in this pass; its earlier accepted review
is H013-collision-baseline.md and H041-fused-work-disposition.md. Search-index
text of Wang–Zhang is not a fresh full algorithm verification, and is not used
to identify its cycle-check mechanism as identical to another implementation.
No claim of an exhaustive current classical-literature search is made.

A subset's density alone does not establish conditional per-trial success
delta in an adaptive walk. IID rejection has mean1/delta, but dependent
selection, accepted-state distribution and collision law need separate proof.
History can be included in state or reconstructibly tracked; it cannot be
assumed irrelevant to coalescence. These qualifications remain as in H040.

Primary access commands included read-only curl --fail --location --silent
--max-time 20 on the EFD shortw and shortw-xz URLs, followed by rg on the
formula entries; both succeeded. The author-hosted co-Z PDF loaded through
web open. No numerical formula benchmark or executable source verification
script was run. Checks on existing Lean artifacts do not certify these paper
comparisons.

## Decision

Retain the specific arithmetic invoices and corrections to the collision
model. No changed complete search algorithm was supplied, so no new numerical
falsifier or broad formal infrastructure is admitted. The next useful object
is a fully specified labelled search/detection schedule with a credible
matched-cost advantage, or another independently proposed solver mechanism.
