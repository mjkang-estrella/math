# R015 — A quadratic-density lower bound for tetrahedral cylinder covers

**Accepted as the ninth substantial finding.** The [I209 proof](../experiments/i209_elliptic_tetrahedron/analytic-attempt.md), sections 2–5, passes the [independent I211 proof review](../reviews/i211-tetrahedron-lower-bound-proof.md) without repairs. The [independent I212 contribution review](../reviews/i212-tetrahedron-lower-bound-contribution.md) supports substantiality with the stronger historical comparison recorded below. The parent read both reviews, checked the key calculations and verified their artifact/source hashes. This acceptance does not certify worldwide priority, human peer review, or a formal proof.

## Exact theorem

Let T be a regular tetrahedron of any edge length e>0. For each i=1,...,N, let u_i be a unit vector and let B_i be a Lebesgue-measurable subset of u_i-perp of finite planar area. If

    T subset union_i (B_i + R u_i),

then

    sum_i |B_i| >= (sqrt(15)/9) A_min(T) = e^2 sqrt(30)/36,

where A_min(T) is the minimum area of an orthogonal projection of T. Bases can be unbounded, disconnected or nonconvex. No assertion of existence of an optimal cover is needed.

For the same tetrahedron, the maximum of

    integral_T q(x) dx /
      [A_min(T) sup_affine_lines ell integral_(ell intersect T) q ds]

over nonzero real polynomials q of degree at most two, nonnegative on T, equals sqrt(15)/9. This is optimality of the specified quadratic-density certificate, not of the covering problem or of arbitrary densities. The lower bound and the certificate optimization are **one finding**.

## Proof

Normalize e=2 and place the centroid at zero. The vertices satisfy |v_i|^2=3/2, v_i.v_j=-1/2 for i!=j. Thus barycentric coordinates give |x|^2=2 sum lambda_i^2-1/2. The volume is 2sqrt(2)/3, A_min(T)=sqrt(2), and the volume mean of |x|^2 is 3/10. The latter follows from mean lambda_i^2=1/10. The minimum projection normalization also follows from the accepted simplex identity A(u)L(u)=3 vol(T) and diameter two; I211 reproduces it independently.

For a>=3/2 put f_a=(a-|x|^2)1_T. A chord with endpoints p,q, midpoint m and length l has integral

    l(a-|m|^2-l^2/12).

If r,s are the endpoints' barycentric vectors, then

    |m|^2 - l^2/4 = 2 sum_i r_i s_i - 1/2 >= -1/2.

Combining this with |m|^2>=0 gives the two cubic upper envelopes l(a-l^2/12) for l<=sqrt(2), and l(a+1/2-l^2/3) for sqrt(2)<=l<=2. The first is increasing; the second is maximized at l=sqrt(a+1/2), or at the endpoint two when a>=7/2. These bounds are attained: the opposite-edge barycentric endpoints (z,1-z,0,0) and (0,0,z,1-z), with 1/2<=z<=1, have disjoint supports and squared chord length 2+8(z-1/2)^2. Therefore the maximum over every direction and every offset is exactly

    M(a)=(2/3)(a+1/2)^(3/2),  3/2<=a<=7/2;
    M(a)=2(a-5/6),            a>=7/2.

At a=19/10 the mass of f_a is 16sqrt(2)/15 and M(a)=16sqrt(15)/25. Tonelli in coordinates u-perp plus R u gives integral_(B+R u) f_a <= M(a)|B| for every measurable base. Nonnegativity and coverage yield mass(f_a)<=M(a)sum_i|B_i|. Their ratio is sqrt(30)/9, proving the asserted bound at e=2. Similarity proves all positive e.

For quadratic optimality, average any admissible q over the tetrahedral symmetry group. This preserves its mass and nonnegativity and cannot increase its maximal line integral. The invariant polynomial is alpha+beta|x|^2. If beta>=0, the edge-line integral bounds its certificate by 1/3. If beta<0, positive rescaling reduces it to f_a with a>=3/2. The normalized ratios are

    (a-3/10)/(a+1/2)^(3/2),   3/2<=a<=7/2;
    (a-3/10)/(3a-5/2),       a>=7/2.

The first derivative changes sign only at 19/10, and the second is negative. The maximum is sqrt(15)/9, attained by the stated density. Symmetrization includes nonsymmetric quadratics without asserting uniqueness of such maximizers.

## What improves, and what remains open

The old general directionwise cylinder bound is 1/3. A stronger old consequence for a regular tetrahedron follows from its inscribed ball: at edge two its inradius is 1/sqrt(6), and the ball theorem gives total base area at least pi/6. Thus the relevant existing consequence is at least

    pi/(6sqrt(2)) ≈ 0.37024,

whereas the new constant is sqrt(15)/9 ≈ 0.43033, about a 16% increase. The prior report's comparison with 1/3 alone was incomplete; this acceptance uses the stronger benchmark. The accepted source's angular construction supplies an upper endpoint strictly below 1/2. The exact covering infimum is still unknown here.

The density method, symmetry averaging, scalar optimization, and ordinary simplex projection identity are credited prior operations. The substantive new bridge is the sharp weighted all-line envelope with its realizing opposite-edge chord family, which gives a new finite-cover inequality for the classical tetrahedral extremal example. I212 found no applicable equal or stronger bound in the primary statements it reviewed; absence of a worldwide duplicate is not certified.

This is an absolute base-area bound. It does not imply the same constant for sum_i |B_i|/A(u_i), and it does not transfer unchanged to arbitrary affine images. It is independent of I203. The failed elliptic upper route in I209 is not part of the accepted proof. The parent I215 higher-dimensional and Gaussian extensions are **not yet independently validated** and are not accepted or counted by this document.

## Sources and validation

- [I211 proof and reading scope](../reviews/i211-tetrahedron-lower-bound-proof.md): verifies every lower-bound step, all measurable-base cases, all directions and offsets, the short-chord regime, both scalar breakpoints and nonsymmetric competitors.
- [I212 contribution and reading scope](../reviews/i212-tetrahedron-lower-bound-contribution.md): compares Bezdek–Litvak 2009 and 2016, Falconer 1980, Akopyan–Karasev–Petrov 2014, the four pinned source companions and bounded survey excerpts. Bang's original paper was inaccessible, and worldwide priority remains unverified.
- [I209 source record](../sources/i209_elliptic_tetrahedron/literature.md) and [I212 source record](../sources/i212_tetrahedron_lower_bound_contribution/literature.md) preserve precise theorem/page ranges and source copies.
- The parent verified final hashes and exact new-source membership, preserved the original submitted reports, and adopted the stronger old benchmark explicitly. No numerical experiment, research code, formal proof check, or audit of the stipulated source truth was used for acceptance.

Pinned corpus: openai/math at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Candidate commit: dabda2d4. Independent proof integration: acbddbe1. This acceptance receives its own commit. **Nine accepted, one remaining.**
