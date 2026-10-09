# H035 shared coordinate and affine-hash fusion

Status: PAPER mechanism, not implemented or measured. Native Sol proposed the
exact-uniform variant independently of root's isomorphism proposal; Astra reviews
algebra/costs. Prior-art/competent-hash comparison is pending. Verified ECDLP
complete-work improvement NONE. H034 source/protocol remain frozen and unexecuted.

## Mechanism and arithmetic boundary

Fix odd prime p and a certified nonsquare nu. Choose theta uniformly in Fp*, a
fair bit e, and independent uniform zeta in Fp. Let kappa=nu^e and
eta=kappa*theta². Then eta is exactly uniform in Fp*. Replace source coordinates
by

    U=eta*x, V=eta*theta*y.

The original curve y²=x³+A*x+B becomes

    V²=kappa^(-1)*U³ + eta*theta²*A*U + eta²*theta²*B.

For a regular pair, d=Ui-Uj and w±=(Vi∓Vj)/d. Thus w± is theta times the
original slope, and with the shared C=zeta-(Ui+Uj), the emitted exact key is

    K± = kappa*w±²+C = eta*x(P_i±P_j)+zeta.

Hash the exact key K by integer reduction modulo the bucket count. Equality of
K is exactly equality of original abscissae; scalar labels/recovery are unchanged.
The two-field refinement above avoids retaining an extra original-x coordinate.
An earlier correct but less economical version cached U=eta*x,V=theta*y and
used the ORIGINAL x-difference. Its extra coordinate/read cost must not be
silently attributed to the improved representation.

When p=3 mod4, choose nu=-1. If e=0, output C+w²; if e=1, output C-w². There
is no need to form a separately negated square. A regular batch of b pairs pays

    fused:    (5b-3)M + 2bS + 7bA + I,
    separate: (7b-3)M + 2bS + 8bA + I.

The separate line is the old6A paired kernel plus two affine hashes per pair.
The new7A consists of one denominator difference, two signed V numerators,
two operations for C, and two output additions/subtractions. This saves
M+0.5A per emitted key AT THIS ARITHMETIC BOUNDARY. Integer branching, bucket
reduction, memory, preprocessing, full-point updates and verification remain.
For a generic nu, the e=1 branch additionally multiplies each squared slope by
nu; over the fair class bit, saving is expected0.5M+0.5A per key instead.
No uniformly cheap nonsquare search is assumed outside the p=3 mod4 case.

Sol's initial M-0.5A saving used unnecessary sign/shift operations. Root proposed
shared C and branch-specific output order; Sol independently recounted and
withdrew the earlier ledger. Both expressions and correction are retained here.

## Scope: every comparator can adopt it

H019 may transform centers, offsets, G and Q with the same representation. The
new cubic is generally NOT the ordinary monic short-Weierstrass model. Complete
addition/doubling, exceptional dispatch, stored full-point updates, certificates
and reference checks must be rewritten or converted honestly. For regular
full-point addition Uout=kappa*slope²-Ui-Uj, Vout=slope*(Ui-Uout)-Vi.
Doubling uses (3*kappa^(-1)*Ui²+new_A)/(2Vi). Prices for those operations do
not automatically equal the paired-key boundary; all extra costs stay charged.

Coordinate transformations cost field operations and initial randomness. Curve
parameters and inverse conversions are paid. Full H019 center refresh costs can
be lower order only under its previously specified growing-block assumptions.
A finite implementation must charge its actual schedule. The two-field proposal
alone is not a measured cache improvement or exact physical-memory claim.

Because eta is exactly uniform nonzero, the previous full-affine pair hash law
is unchanged for fixed distinct geometric keys. The stopping/edge order must
remain independent of table hashing; changing a coordinate-based walk selector
would require a new trajectory analysis. Fixed deterministic PRNG samples do
not instantiate the ideal IID proof automatically.

## Independently derived square-only alternative

Root separately proposed X=u²*x+zeta,Y=u³*y, whose curve is
Y²=(X-zeta)³+u⁴*A*(X-zeta)+u⁶*B. Regular addition yields
Xout=slope²-Xi-Xj+3zeta. Sharing Xi+Xj-3zeta also gives7A per pair and no
separate affine multiplication. Its horizontal multiplier is square-only.

Astra's exact collision correction, independently recognized by root, is as
follows. For any fixed bucket partition B_j, put

    C0=sum_j |B_j|*(|B_j|-1),
    Z=sum_j sum_{a!=b in B_j} chi(b-a).

For fixed original difference delta!=0, square-affine hashing has collision
probability (C0+chi(delta)*Z)/(p*(p-1)). For p=3 mod4, reversing every ordered
within-bucket pair cancels Z exactly, so the FULL-AFFINE pair collision value
is retained. This does not make the ordered hash outputs jointly uniform.
For p=1 mod4 only the bound2*C0/(p*(p-1))<=2/H is established without further
estimates. Hand-checkable counterexample p5,H2,delta2 gives probability3/5,
above1/H. Hence a universal square-only1/H claim would be false.

The exact-uniform variant avoids this field-congruence qualification in its
probability law, at the stated possible generic-nu multiplication cost.
Neither variant establishes improvement over a competent cheaper word hash.

## Other independent mechanisms and their cheap falsifiers

Sol's completed initial ideation also supplied two distinct mechanisms. Both
are retained instead of inflating the surviving pool with variations of fusion.

1. Common-root row locality. Loading one fixed line root once per ell-edge row
   uses2ell+2 input field words, or1+1/ell per emitted key, instead of two.
   H019's fixed-offset round over k centers analogously uses2k+2 words,
   or1+1/k per key. Thus a matched optimized schedule removes the apparent
   candidate-specific locality advantage. Root confirmed these word counts for
   the stated two-coordinate input model; they exclude all other memory traffic.
   Copying roots into edge order would add leading construction/storage costs.
2. Unnormalized paired-output quadratics. For delta=xi-xj and
   N=(xi+xj)*(xi*xj+A)+2B, the polynomial

       Fij(X)=(delta²*X-N)²-4*yi²*yj²

   has exactly the two ordinary paired abscissae as roots, when delta!=0.
   Root checked this by substituting the paired affine formulas and curve
   equation. With per-root y² prepaid, expanding its three coefficients takes
   4M+3S plus additions per edge: two M for N, one for delta²*N, one for
   yi²*yj²; squares delta²,delta⁴,N². Avoiding inverses does not supply a cheap
   collision detector. Pairwise resultants cost quadratic many tests, and a
   classical product tree's largest polynomial multiplication costs quadratic
   field work. Faster polynomial multiplication is a paid algorithm, not a
   free primitive. Witness localization and first-event/overshoot semantics
   remain unresolved. H019 can use the same polynomials with cross-role
   intersections. No complete detector with favorable work was proposed.

These are scoped paper negatives for the literal schedules/detectors, not a
universal memory or polynomial-method lower bound. No tests or imports occurred.

## Next decisive review and process

New Claude Opus5.5 primary prior-art/comparator review RUNNING:
`node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h035-hash-fusion-priorart-opus-20261008-r1`.
Its brief contains the earlier correct three-field variant. The later two-field
refinement will be supplied in a NEW round if the returned critique depends on
that difference; no backing-child messaging continues a review round.

Root bounded web searches for EC isomorphism/hash and square-multiplier hashing
found no directly verified prior-art source for this exact fusion. That is NOT
novelty evidence. No technical conclusion here relies on search snippets.
The review must compare conventional word/multiply-shift/tabulation alternatives,
including their actual distribution assumptions and complete price. If they
already avoid the paid field multiplication, this named comparator saving may
have no practical relevance. No source change or numerical run follows yet.
