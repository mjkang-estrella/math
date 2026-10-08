# H002 constraint proposals: distinguish observations from recovery

Native Astra `/root/encoding_review` independently reviewed the four Grok cards,
primary sources, and root objections. No experiments or edits. No complete-work
improvement; all four lack an explicit recovery/witness algorithm. Retain their
speculative kernels and scope the proposed falsifiers, rather than declare broad
coordinate approaches impossible.

## C1: periodic net-block inversion

Root's initial objection to the odd recurrence's indexing was WRONG: substituting
m=i−1 into the standard odd recurrence gives exactly the raw card's formula.
Its numerator is quartic, not cubic. Distinguish pointwise phi(nG), whose corrected
exponent is n², from phi(nG)/phi(G), whose exponent is n²−1 and is normalized
for those recurrences. Source: [Lauter–Stange](https://arxiv.org/pdf/0803.0728).

Pure doubling already has a unique inverse on the prime odd-order subgroup,
namely multiplication by(q+1)/2. This does not reveal canonical scalar bits.
Both inverse-double(Q) and inverse-double(Q−G) exist; choosing the branch that
belongs to a canonical integer prefix is the missing primitive. Degree of a
composed algebraic map alone is not the cost of solving that selection problem.
With t≈log2(q), work2^(c*t) only beats sqrt(q) when c<1/2 after all costs, not
merely c<1. Mean branching<sqrt2 is not necessarily polynomial. No finite four-
degree sample gives a family-wide impossibility theorem. Retain only a concrete
canonical-prefix discriminator; otherwise overlap A1's scalar-information gap.

## C2: sparse ANF of a coordinate bit

A degree-n monomial has one term and a small circuit: high degree does not prove
hardness. Define the function on every2^n Boolean input, including k≥q, identity,
and zero Legendre symbol, before discussing ANF support. Different extensions
change it. One linear coordinate bit gives one equation, not n-bit inversion.
Need enough observable constraints, an explicit learning and inversion algorithm,
and its actual polynomial exponent in term count T. T<sqrt(q) does not suffice
if the algorithm costs T² or worse. Dense support rejects that exact sparse
representation; degree alone does not. No ANF survey funded without this bridge.

## C3: four-list merge through coordinate prefixes

The relevant mutual information is I((X_P,X_Q);X_(P+Q)). Eight-bit tags give
2^24 joint cells, and10k samples can give spurious plug-in information even for
independent variables. More fundamentally, nonzero information supplies neither
a composable filter retaining real solutions nor cheap enumeration of surviving
pairs. Product-tree membership of supplied values does not generate values from
L² implicit pairs at quasi-linear cost. A null for a particular feature only
rejects that feature-based route. Require an actual survivor-generation procedure
with yield, false-negative and complete pair-generation costs. Overlaps H001's
coordinate-bucket/join gate; raw MI pilot not accepted.

## C4: fixed tuple tester versus factor-base decomposition

For fixed m, supplied valid x-coordinates can already be tested by point lifting
and at most2^m sign choices. Finding ANY witness in F^m for a target is different.
The heuristic relation budget is `(q/f^(m−1))*C_decompose + C_linear_algebra`,
under its distribution/rank hypotheses. A tiny tuple tester does not make
C_decompose small. At fixed m, degree2^m is constant in q. Gcd/resultant schemes
must encode factor-base membership and extract witnesses, charging construction,
degrees, storage and failed trials. Random tuple labels test the easy predicate
and can contain almost no positives. Retain only an actual witness-producing
procedure; this currently repeats the unresolved Semaev generator requirement.

## Scope and next action

Prime rational group order does not exclude small rational isogenies: their kernels
need be Galois-stable, not pointwise rational. Reviewer retrieved [Banegas et al.,
§§2,5](https://arxiv.org/pdf/2306.16072). An isogeny alone supplies no DLP gain.
Ideal quotient collision-count constants are not complete-work speedups.

Verdict: no raw degree/MI/grammar pilot approved. These criticisms do not reject
originality for lacking a proof: they identify the precise missing executable
steps. Current cheap test remains the specific A1 diagnostic, with noisy recovery
still a separate obligation. No generic Lean infrastructure is needed here.
