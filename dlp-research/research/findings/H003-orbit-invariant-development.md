# H003 A3: explicit invariant constructions and their costs

Native Astra `/root/h002_arithmetic_ideas` developed three concrete constructions
after the initial A3 proposal and independent orbit review. No edits, experiments
or children. Root checked the telescoping algebra and scoped the conclusions.
Verified ECDLP improvement NONE; these are explicit failures of proposed routes,
not a universal coordinate-invariant lower bound.

## Shared recovery, including delayed transporters

An exact H-invariant label F permits scalar multiplicative transitions
X←[c_partition(F(X))]X, with scalar coefficients a,b updated by the same c.
This respects equivalence, but mixing/useful collisions are NOT established.
Cross-start collision X_i=[t]X_j gives
`k=(t*a_j−a_i)/(b_i−t*b_j) mod n` when the denominator is nonzero; verify kP=Q.
Same-start multiplicative collisions are generally fruitless. Action-BSGS can
recover t∈⟨lambda⟩ with sqrt(m) points, but its giant multiplier costs a scalar
multiplication unless a genuinely cheap map is provided. Do not price every
transporter step as a cheap endomorphism. Count setup, labels, transitions,
every attempted collision, fruitless recovery, replay and restarts. Only a
justified mixing model permits sqrt(n/m) quotient-step estimates.

## D1: return derivatives give an exact constant

Let f_d be the x-map of[d], with d prime to n, and choose h with d^h=epsilon mod n,
epsilon=±1. For nonzero points in an odd prime-order subgroup, y is nonzero.
The invariant differential yields
`f_d'(x(R))=d*y([d]R)/y(R)`.
Multiplying around h iterates telescopes to `epsilon*d^h mod p`, independent
of R. It is cheaply computable by modular powering, but separates no classes.
Root independently checked that product and its hypotheses; no point experiment
is needed. Handle inseparability as zero derivative, not a new useful label.

Translation to the formal origin conjugates the local return map to multiplication
by[epsilon*d^h]. Thus invariants of that local conjugacy type also do not separate
these points. Raw coordinate jets can vary; they are not automatically orbit
invariants. This rejects the specified local-dynamics shortcut, not arbitrary
global orbit circuits. For a proposed product of g over an orbit, first check
whether g is a multiplicative coboundary u∘[d]/u times a constant: the same
telescoping failure may apply. No broad jet or Lean infrastructure funded.

## D2: pairing and Frobenius-orbit polynomial

Let e=ord_n(p), use K=F_(p^e), and a nondegenerate pairing homomorphism z(R) into
mu_n(K). The polynomial ∏_(0≤j<e)(T−z(R)^(p^j)) exactly labels ⟨p⟩-orbits.
Choose the smaller coefficient vector for z and z^(-1) to include negation.
Maintaining z(P)^a*z(Q)^b avoids repeated pairings; collision recovery enumerates
Frobenius conjugates and yields t=±p^j. A trace alone may have false collisions.

This handles H=⟨p,−1⟩, not arbitrary ⟨2,−1⟩ on rational points. In an explicit
degree-e extension, even favorable arithmetic handles e coordinates; a naive
polynomial construction costs O(e² M(e)) base-field work, and final exponentiation,
field/basis construction and nondegenerate pairing input search are not free.
Those are costs of the proposed implementation, not all compressed representations.
Compare the established direct finite-field DLP transfer as well as EC rho after
the same setup. No large-embedding-degree speedup follows, and favorable special
embedding degree is already relevant to the known pairing baseline.
Proposer reference: [MOV](https://doi.org/10.1145/103418.103434).

## D3: Reynolds projection in a large coordinate algebra

Set N=(n−1)/2 and D(X)=∏(X−x(R)) over nonzero subgroup points modulo negation.
In A=F_p[X]/D, represent the lambda x-action by f. For orbit length h and seed b,
F_b=Σ_(j<h) b∘f^j is invariant. Binary blocks satisfy
`G_(2r)=G_r∘G_r`, `S_(2r)=S_r+S_r∘G_r` modulo D, hence O(log h) modular
compositions. They operate on degree-N polynomials, not constant-cost objects.

Explicit setup enumerates O(n) subgroup points, stores O(n)-scale data, and builds
D. Random full-degree seeds give probabilistically separating orbit sums, but
constructing/storing/evaluating them costs degree-N algebra work. Horner queries
cost O(N); batching does not erase setup. A precomputed orbit table uses the same
enumeration that already permits a full scalar dictionary for the matched baseline.
Leaving the recurrence unexpanded requires evaluations at distinct inputs and
expands to h leaves unless another evaluation identity exists. Short recursive
notation is not cheap evaluation. Elliptic periods are prior art; proposer cites
[finite-field embeddings, §5](https://cs.uwaterloo.ca/~eschost/publications/ffisom.pdf).

## Decision

Close D1 analytically. Retain D2/D3 as useful exact constructions with unfavorable
current complete costs; do not claim every future compressed representation is
impossible. A surviving A3 submission must give a concrete nonconstant orbit sum/
product evaluation identity avoiding both n-scale setup and h leaf evaluations.
Testing a specified low-order recurrence could reject that recurrence only; no
unfocused rank survey is authorized. No such cheap identity emerged in this wave.
