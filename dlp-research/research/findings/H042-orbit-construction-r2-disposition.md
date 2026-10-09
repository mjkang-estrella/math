# H042 orbit round2: known-log decomposition does not inherit density

2026-10-09 UTC. Raw report: H042-orbit-construction-r2-raw.md. No claimed
complete-work survivor. Native Astra independently confirmed the mathematics;
native Sol confirmed the cost and witness accounting. No numerical run, Lean
claim or H034 cap reset.

## Exact recovery versus unjustified comparison

A paid known-log set is valid synthetic algorithm input: generate points with
public scalars, retain their x-coordinate/sign lookup, and charge setup/storage.
If an extracted and verified decomposition gives

    aG+bQ = sum_j epsilon_j [s_j]G,   b!=0 mod q,

one recovers k=(sum_j epsilon_j s_j-a)/b mod q and verifies [k]G=Q. A relation
with right side -R requires changing its signs before this formula. R=O must
be dispatched directly. Repeated indices with opposite signs can cancel even
when all DISTINCT stored abscissae are different; aggregate the coefficients.
The doubling orbit also has P_i+P_i-P_(i+1)=O, so even its specific scalar
structure gives cancellations not excluded by the multiplicative order test.

For powers s_i=ell^i, a verified order condition ord_q(ell)>2B is sufficient
for the first B stored abscissae to be distinct. An actual duplicate check can
replace that sufficient condition. Neither test proves additive expansion or
decomposition success probability. Roots of a membership polynomial being
rational alone also does not establish a valid elliptic-curve relation. Here
the roots were generated from known curve points; use that fact, an exact
summation-polynomial equivalence and verified sign extraction, with exceptional
branches dispatched. Do not silently omit witness work.

The valid conditional invoice is A_known+D_known/sigma_known+recovery, when
independent attempts or an appropriate conditional cost/success argument
justify it. Deleting unknown factor-base columns can remove linear algebra.
But a fair baseline given the SAME known logs can do exactly that too. A PKM
factor base whose logs are unknown is a different input geometry; equal degree
does not establish equal replay cost or success probability. The raw 'genuinely
beats its matched baseline' statement is therefore not supported.

## A decisive density counterexample

Take S={[j]G:1<=j<=B} in an odd order-q subgroup, with 2mB<q. Every signed
m-term sum has scalar in the integer interval [-mB,mB], hence the entire
reachable target set contains at most2mB+1 points. An independent uniform
target therefore has decomposition probability at most(2mB+1)/q.

For m=2 and B of square-root scale (and sufficiently large q), this probability
is O(q^(-1/2)), not a constant. Thus the raw assertion that an arithmetic
progression behaves like every other known-log set is false. No finite
experiment is needed for this named example; the interval bound proves it.
It does not estimate the sumset of the power-of-ell construction.

For any fixed coefficient pattern and ordered B0^m tuples, averaging the
number of witnesses over uniform R gives exactly B0^m/q. This elementary
count is not the probability of at least one witness: many tuples can have the
same sum. It establishes neither rank nor time to find a witness. Equal means
across patterns or factor bases therefore do not establish equal sigma or D.

## The named polynomial schedules

At m=2 the report names a concrete operation: multiply the quadratic-in-X1
polynomials S3(X1,x(P),x(R)) over the B stored points and take a gcd with L_V.
With fast polynomial arithmetic, this has a soft-linear field-work upper bound,
plus extraction and verification. Evaluate the gcd on stored roots to locate
one candidate, retrieve its point P1, and look up partners R+P1 and R-P1 in the
stored point/sign table. Verify the signed sum and scalar result. Full points
and public labels must be stored or reconstructed at paid cost; no quadratic
witness scan is forced for this explicit representation. No constant success
probability follows from B alone.

For fixed m>2, a FULL scan of m-2 choices followed by this two-variable routine
has the modeled work B^(m-1), up to constants/logarithms and witness handling.
Even in the additional ideal model sigma comparable to min(1,B^m/q), its
modeled attempt cost divided by sigma is

    q/B                 when B<=q^(1/m),
    B^(m-1)             when B>=q^(1/m).

Balancing q/B with setup B at B=sqrt(q) is outside the first regime for m>2.
The minimum of this FULL-SCAN model occurs at B of scale q^(1/m), giving
q^(1-1/m), worse than square-root for m>2. At m=2 it recovers square-root
scaling under the same success assumption. This is an invoice for that stated
scan, not a lower bound for early stopping, shared work or arbitrary solvers.

The raw intermediate-orbit formula also holds D, sigma and rank fixed while
changing the factor base. These are unproved hypotheses, so it cannot prove
that full collapse dominates every intermediate layer count. Sharing does not
force one unique dense-polynomial representation: composed constraints and
selectors are among alternatives whose actual costs would need analysis.

## Decision

Retain the one-relation recovery identity and the explicit density
counterexample. The construction did not supply an operator with a justified
complete-work gain. No further construction round or experiment is admitted
for this card absent a changed decomposition method or proved useful yield.
This parks the submitted implementation; it does not rule out orbit-assisted
relation generation as a class. Verified improvement NONE; exponent1/2 remains
the reference. No fresh literature or novelty claim was provided by the proposer.
