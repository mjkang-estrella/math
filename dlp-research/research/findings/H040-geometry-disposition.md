# H040 state geometry: no new successor supplied

2026-10-08. Verdict: no admitted algorithm or experiment. The raw Grok4.7
proposal is retained in H040-geometry-grok-raw.md. Native Sol
`/root/h034_c4_implementation` independently reviewed the scope, read-only;
root checked the elementary identities and read the primary negation paper.
No runs, executable imports, new Lean claims or H034 cap reset.

## Accepted corrections

Let the subgroup have odd prime order q. The affine involution
I_B(P)=-P-B has one fixed point -B/2, with all other orbits of size two.
Its quotient therefore has (q+1)/2 states. The raw report confuses orbit size
and quotient cardinality. It is translation-conjugate to negation, so an
extra addition on every step is not mandatory: representation/setup may move
that cost. There is no extra quotient-size gain from this involution alone.

Composing it with negation gives translation by B or -B. For B nonzero this
generates a transitive action. A constant representative is easy, but useful
DLP recovery needs a recoverable label or transporter. No inexpensive operation
providing that information was submitted. This is a missing construction, not
a coordinate-aware impossibility theorem.

For x(W) != x(J), the usual two addition slopes prove

    x(W+J)+x(W-J)
      = 2(y(W)^2+y(J)^2)/(x(W)-x(J))^2 - 2(x(W)+x(J)).

The sum is a field-valued feature, not automatically a group point with affine
labels. Equality of two such sums does not by itself give the ordinary linear
recovery equation. The actual side point W-J does have recoverable labels.
Whether its collision is detected or coalesces depends on the named successor
and detector; the raw categorical rejection of side-image coalescence is too
broad. Exceptional addition branches also need dispatch. No useful-collision
increase paying for the extra work was established.

A successor depending on past history need not be a function of the present
point. History must be included in the state, reconstructed, or proved irrelevant
to future transitions. Point equality alone then need not imply coalescence.
Neither the enlarged state's cardinality nor its collision law follows by
declaring it a window of points. This corrects the raw 'another partition
function' claim without excluding useful controllers.

For rejection sampling, if each trial has conditional acceptance probability
delta, its expected trial count is 1/delta. Under an additional uniform
accepted-state birthday model on delta times the negation quotient, this gives
the ideal work scale sqrt(q/delta). Density alone establishes neither premise.
Specify whether density refers to points or negation classes. An adaptive cheap
projection is outside that argument; none was provided here.

The only-usable-automorphism-is-negation premise is a family restriction, not
a consequence of being ordinary over a prime field. Applicable extra symmetries
must be used in both candidate and comparison algorithms. Labels may be stored
explicitly or recovered through paid replay. A detector need not eliminate both
record storage and reporting delay: a material improvement in matched total
work would suffice. No such construction was submitted.

## Primary-source scope

Root read Bernstein, Lange and Schwabe, [On the correct use of the negation map
in the Pollard rho method](https://cr.yp.to/elliptic/negation-20110102.pdf):
'Use of group automorphisms', distinguished-point discussion, lazy coefficient
recovery, fruitless-cycle analysis and Appendix A. The paper explains compatible
small-order automorphisms, recoverable endpoint coefficients and replay; its
additive-walk cycle overhead is scoped to the analyzed construction. Appendix A
discusses multiplicative walks with small integer multipliers and their higher
arithmetic cost. These are established baselines, not discoveries or universal
lower bounds on new walks. Koblitz/Frobenius exceptions do not transfer without
their field/curve hypotheses. No current hardware throughput follows.

The browser PDF open returned502; the primary URL succeeded with:

    curl --fail --location --max-time 20 --silent https://cr.yp.to/elliptic/negation-20110102.pdf | pdftotext -layout - - | rg -n -A 28 -B 6 'Use of group|multiplicative|Theta|Θ'

The root also checked the accepted H013 collision ledger; batched field costs
do not remove logical cycle/history/restart requirements. H038's bounded
recovery-graph screen does not cover an unrestricted long rho trajectory.

## Wave result and reopening gate

Best supported exponent remains1/2 with applicable known automorphism constants;
verified complete-work improvement NONE. H040's independent algebraic,
information and geometry proposals produced no admitted survivor. Their narrow
negative findings do not establish general ECDLP hardness.

Next conclusion-changing evidence is an explicit public transition or recovery
operator, full state and label update, a useful nonzero-coefficient collision
law or correctness argument, and paid preprocessing, cycles, detection, replay,
memory and verification. Only a survivor of this gate warrants a new bounded
synthetic experiment. No generic formal infrastructure is requested.
