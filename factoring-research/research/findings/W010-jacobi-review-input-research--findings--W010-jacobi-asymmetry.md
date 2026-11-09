# W010 — Jacobi-controlled local asymmetry

Post-review steering: the unfiltered sampler now has a proved positive
expected-drift theorem; see W010-norm-cubic-disposition.md. That theorem
does not transfer through this character filter. A concrete symbolic
counterexample is recorded below. The acquisition and no-full-gcd identities
remain provisional pending their separate audit.

2026-10-08. Parent constructive extension, PROVISIONAL and not included
in the frozen first W010 audit. No experiment or factoring improvement.
This makes a local splitting-type difference executable without supplying
either prime or a Frobenius map. It also exposes its rejection cost.

## A concrete N-only selector and an unmasked new-root test

Use the same two sampled values, unit/distinct/opposite checks and
beta=z^2+z*u+u^2 as W010. Additionally test gcd(beta,N).
Return a proper gcd, retain a full gcd as a paid no-op, and on a unit
beta compute the ordinary Jacobi symbol (beta/N). Perform the cubic
update only if that symbol is -1; +1 is another paid no-op.

For a remaining odd squarefree N=pq this guarantees exactly one of
chi_p(beta),chi_q(beta) is positive. At the nonsquare component,

    P(x)^3-beta*P(x)=0 iff P(x)=0.

At the square component new roots may be added. In particular the
separately tested quadratic factor has the exact property

    gcd(P(x)^2-beta,N) cannot equal N, for any x.                   (1)

If it vanished at both primes, beta would be a square at both, contradicting
its Jacobi symbol. This even holds without assuming P(x) is a unit.
Testing the whole cubic product instead could mask an old root at the
other prime; the quadratic factor must remain a separate gcd channel.

This eliminates full-gcd ambiguity for the new-root factor. It does not
make those roots numerous in the current image or make their preimages
cheap. The two local orientations may alternate across stages; the
Jacobi symbol does not reveal which prime has which sign.

## Exact raw selection laws instead of a uniform-beta assumption

For each local current map use K,A,B from the original W010 proposal.
Define unnormalized masses

    L_+=sum_(chi(beta)=+1) K(beta),
    L_-=sum_(chi(beta)=-1) K(beta),  Z=K(0),
    G=sum_beta K(beta)*B(beta),
    D_+=sum_(chi(beta)=+1) K(beta)*(K(beta)-A(beta)),
    D_-=sum_(chi(beta)=-1) K(beta)^2.

Then ell=L_++L_-+Z. B and A vanish off the positive class.
For a fixed complete current map modulo N, fresh CRT pair sampling
gives exact probability of an accepted update

    C=L_(p,+)*L_(q,-)+L_(p,-)*L_(q,+).                              (2)

The unconditioned raw moment changes of the full-tape/no-op process are

    E[Delta m_p | map]=L_(q,-)*G_p,
    E[Delta v_p | map]=L_(q,-)*D_(p,+)+L_(q,+)*D_(p,-),             (3)

and the symmetric formulas at q. The negative-character sector has no
root-removal penalty, so D_- is nonnegative. D_+ need not be.
Conditional accepted-update formulas divide (3) by C only if C>0.

The beta gcd contributes an additional early-factor probability, after
both anchor charts are locally legal, of

    Z_p*(L_(q,+)+L_(q,-))+(L_(p,+)+L_(p,-))*Z_q.                    (4)

Both beta components zero has probability Z_p*Z_q and yields a full gcd.
Earlier anchor checks have their own success and failure outcomes and
are not included in (4). The +1-Jacobi rejections are paid even though all
values are units. Neither C nor a conditional drift is a complete success
or expected-work law. Survived histories remain correlated.

## The free start reveals the cost immediately

For uniform affine input, write epsilon=chi(-3), h=chi(3),
C0=p-epsilon-4 and D0=3+h. The proposed conic counts from W010 give

    L_+=(p-1)*(C0-D0)/(2p^2),
    L_-=(p-1)*(C0+D0)/(2p^2),
    Z=(p-1)*(1+epsilon)/p^2,
    G=2*L_+/p.                                                   (5)

As p,q grow, the accepted-update probability in (2) tends to 1/2.
The root increment at p per raw attempt is about 1/(2p), whereas the
unfiltered sampler has about 1/p. Per ACCEPTED update it is again about
1/p. Thus the filter does not improve first-step root supply and discards
roughly half the raw attempts. Small primes can have L_+=0 and must not
be described by this asymptotic approximation.

The precise possible saving is later: exploit a weighted law in which
the selected negative sector concentrates useful residual mass while
the positive sector exposes substantial new root mass, and (1) prevents
masking that new-root gcd. Such a law, its reachable acquisition and
the full cost have not been established. This selector alone is not
grounds for a benchmark or a speedup claim.

## Next decisive comparison

First verify (1)-(5) and combine them with the independently audited W010
law when that review arrives. Then compare RAW paid progress of the
filtered and unfiltered processes on an analytically specified reachable
family; normalizing away half the attempted updates is invalid.
An arbitrary distribution counterexample or favorable subgroup is not
a substitute for that family. This avenue retains the intended local
asymmetry without pretending that a Jacobi symbol splits its two factors.

## Parent falsifier for inheriting positive drift

The following is an exact proposed distribution certificate, not a W010
candidate run or a reachable-history assertion. At p=167 use masses t on
each of +-3,+-5 and H on each of +-7. The original review's six norm
parameters are 49,19,79,37,109,39. Here 49 and 19 are squares, and
79,37,109,39 are nonsquares. The root-removal term occurs only at 49.
Consequently

    L_(p,+)=8t^2,  L_(p,-)=16tH,
    D_(p,+)=32t^4-8t^2 H^2.

At q=5 with the uniform starting map, L_(q,+)=0, L_(q,-)=8/25.
Choose t=1/12,H=1/4,m=1/6. Then D_(p,+)=-5/2592 and the filtered
RAW drift at p is -1/1620. Its clean update probability is 4/225,
so its conditional drift is -5/144. In contrast, the unfiltered local
drift is positive. All these rational-mass statements are about arbitrary
symmetric distributions, not uniform finite-field pushforwards.

There is also a version with integral fiber counts at p: t=14/167,
H=42/167,m=27/167. These masses can be an odd-map pushforward, and give
D_(p,+)=-40t^4<0, with conditional drift -5t^2. Interpolating an odd
function does not show it is generated by the cubic acquisition protocol;
reachability remains unclaimed. The certificate falsifies only the
automatic extension of the universal symmetric-law drift theorem.

Constructive response: preserve the unfiltered training law and, if useful,
apply the Jacobi selector only in a separately priced final detector.
That keeps the accepted training invariant but still must pay for endpoint
parameter acquisition, rejected attempts and actual new-root density.
