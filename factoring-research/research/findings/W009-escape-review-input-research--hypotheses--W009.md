# W009 — three sampled anchors for a rational fiber merger

2026-10-08. Parent constructive candidate; PROVISIONAL and not installed.
No experiment is selected yet, and no improved factoring complexity is claimed.
This changes the update rule, rather than extending the independent polynomial
tower whose early-depth envelope is now under audit.
Initial scope is N=pq with distinct odd primes, after paid fixed small-prime
removal. General composites need a separate extension.

## Executable update, not a sampling oracle

Carry a rational map P as a projective circuit, initially P(X)=X. Evaluate
it on three fresh uniform residues, obtaining affine values a,y,w on a
legal unit chart. Test all needed denominators and a,y,w,y-w by gcd before
inversion. A proper gcd is a factor; a full-gcd chart failure is retained
as a failed attempt. Compute

    t=(a-y-w)/(y*w),
    F_(a,t)(z)=z*(z-a)/(1+t*z),
    P_new=F_(a,t) composed with P.

The two by two matrix of

    iota(z)=(a-z)/(1+t*z)

squares to (1+a*t) times the identity. Test gcd(1+a*t,N) as well; a
proper gcd returns a factor, a full gcd fails this chart. These checks
also make a-y and a-w units, since 1+a*t=(a-y)*(a-w)/(y*w).
Thus the two planted orbits are distinct on both prime components.
On the unit chart it is an involution, and

    iota(0)=a, iota(a)=0, iota(y)=w, iota(w)=y,
    F(iota(z))=F(z).

Thus one sampled fiber joins zero and two other actually sampled fibers
merge in the same update. The second merger changes future fiber mass;
it does not itself add a root. This differs from planting a root and
hoping an unrelated nonzero pair happens to merge.

If P is represented at a point by [U:V], its next value is

    [ U*(U-a*V) : V*(V+t*U) ].                           (1)

This needs only a fixed number of modular operations per stage. No
per-point modular inversion is necessary, and gcds of U,V and the
displayed factors retain both root and pole opportunities. The parameter
acquisition uses three actual evaluations per stage, hence O(k^2) modular
work through depth k with the explicit chain. One probe still costs O(k).
Every failed chart, gcd, inverse, parameter and operand width must be paid.

## The changed incidence, and the saving it would have to supply

For finite values z,u on a legal chart,

    F(z)-F(u)
      =(z-u)*(z+u+t*z*u-a)/((1+t*z)*(1+t*u)).            (2)

Substituting the acquired t gives the merger condition

    a*(z*u-y*w) + y*w*(z+u) - z*u*(y+w) = 0.            (3)

The ordinary polynomial tower tests z+u=a. This new update uses the
quadratic incidence (3), with a parameter obtained from three samples.
It could improve full time only if these paid anchors cause many OTHER
heavy fibers to merge, persistently, with different useful behavior at
the two CRT primes. One planted pair alone is insufficient: before
conditioning on legal charts, its ordered-pair mass is at most 2*c^2,
where c=sum mu(v)^2. At a nearly uniform start this is O(1/p^2), whereas
the background merger mass is already O(1/p). Treating the guaranteed
pair as a constant-factor amplification of c would be a false gain.

For a fixed projective law mu and a nondegenerate involution, the exact
pushforward collision mass is

    c_new=c + sum_z mu(z)*mu(iota(z))
              - sum_(z=iota(z)) mu(z)^2.                (4)

Both sums are on the projective line. This includes poles; pretending
that all outputs remain affine would lose a growing atom at infinity.
The zero atom absorbs the a fiber, and the infinity atom absorbs the
fiber at -1/t (with projective conventions when t=0). A useful statistic
must exclude mass already trapped at BOTH atoms, as appropriate for later
factor tests. The earlier polynomial residual formula cannot be reused.

## Costs and decisive first gate

The possible saving is higher useful mass per O(k^2) acquired circuit,
not a cheaper circuit evaluation. Unknown factors, projective image laws,
heavy-fiber selectors and square-root oracles are not inputs. The value
1+a*t=(a-y)*(a-w)/(y*w) makes several degeneracies and early gcd channels
explicit; they must not be silently conditioned away in success estimates.

The first cheap falsifier is a symbolic averaged version of (4), using
the actual three-sample distribution and the rejected-chart probabilities.
Separate the two forced orbits from all other solutions of (3). Determine
whether the non-forced contribution is only the ordinary O(1/p) merger
rate plus O(c^2), or contains a stronger reachable correlation. At a
uniform projective input, (4) gives 2/(p+1)-f/(p+1)^2, with f=0 or 2
fixed points; that familiar first-step doubling proves no persistent gain.
This is a diagnostic law, not the actual initial sampling distribution.
For the actual uniform AFFINE start, mu(infinity)=0: when t!=0 modulo p,
(4) instead gives (2p-1-f)/p^2, with f=0 or 2 affine fixed points. One
finite input is paired with infinity and contributes no collision partner.
When t=0, the value is (2p-1)/p^2, the ordinary polynomial-fold value.
Thus this update does not improve initial collision mass over that control.
Its potential difference lies in later incidence and pole acquisition,
whose persistent useful growth is still unproved.

No prime sweep or factoring benchmark is justified by the identities
alone. First derive the law and a complete finite-field chart protocol.
A later test, if warranted, needs a separate preregistration that counts
all failures, poles, and early gcds. This candidate is not the earlier
fixed norm-one torus map/menu; neither its accepted sign obstruction nor
its probability law transfers without a new argument.

The parallel scalar-product direction remains active: it tries to reduce
the detector's work rather than amplify roots. This acquisition candidate
should not displace it merely because its circuit has exponentially
growing formal degree.
