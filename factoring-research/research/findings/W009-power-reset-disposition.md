# W009 power reset — parent disposition

2026-10-08. Independent D review consumed. All 26 delivery hashes verified.
The original proposal and frozen review inputs are preserved. This disposition
governs the accepted scope. No factoring improvement or candidate run.

Accept the review's proof of equations (1)–(4): for distinct nonzero anchors,
the four zero/pole fibers of F(Z)=(Z-y)(Z-w)/Z prevent F(P) from being an
ell-th power for every prime ell different from the characteristic. If
P=S^(p^a) with S separable, the divisor multiplicity gcd of F(P) is p^a.
Consequently F(P)^e is a geometric d-th power, d dividing p-1, exactly
when d divides the last accepted exponent e. Earlier exponents do not
accumulate this geometric resource through subsequent distinct-anchor folds.
Paid no-ops change neither the map nor the controlling exponent.

The proof correctly uses the different inequality in wild ramification,
Frobenius roots of the anchors for inseparable maps, and full divisibility
for composite d. The equivalent normalized Kummer cover has genus ell-1.
The primary Riemann–Hurwitz and character-sum sources are pinned in the
[review](W009-power-reset-review.md); its 12 exact checks are algebraic
certificates, not candidate performance evidence.

Accept the character bound |M_R(psi)| <= (4D-1)/sqrt(p) and exceptional
energy decomposition with g=gcd(e,p-1). The degree-dependent error can be
useless at large D. O(log e) point powering does not make that error small.
These statements do not supply useful exponents, root supply, CRT separation,
or a success recurrence. Geometric non-power does not rule out exceptional
finite-field values: the review's F_5 example demonstrates the distinction,
but its unavailable anchors make it no reachable-history example.

Repair the original support-boundary prose as follows:

- Four supporting values obstruct all prime root orders other than p;
  three already obstruct orders ell>=3.
- Count divisor support values whose valuations are coprime to ell,
  not all support values or critical values.
- For squares the number of odd valuations is even. The allowed number
  under this necessary bound is zero or two, never exactly three.
  The coalesced map has three total support values but only two odd ones.
- The generalized inequality requires ell!=p. For inseparable degree p^a,
  use separable degree D0 first: r D0(1-1/ell)<=2D0-2. Multiplication by
  p^a yields the stronger total-degree bound 2D-2p^a, hence the proposed
  2D-2 bound as a weaker consequence.

Constructive consequence: compounding geometric powers is closed for this
specific fold. A different divisor pattern or acquired finite-field correlation
would be needed. Coalescence was tested separately in E; it must not inherit
the distinct-anchor sampler law. No general factoring lower bound follows.
