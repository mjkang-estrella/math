# I209: a quadratic-density lower bound for tetrahedral cylinder covers

2026-10-12. **PROVED NOMINATION, with an unresolved upper-cover route.** Every finite cylinder cover of a regular tetrahedron T satisfies

    sum_i |B_i| >= (sqrt(15)/9) A_min(T).

Moreover, sqrt(15)/9 is the optimal lower certificate obtainable from a nonnegative polynomial density of degree at most two on T using a single uniform bound on its line integrals. These are one connected proposed contribution. The parent retains both acceptance gates; eight findings remain accepted and no count is incremented here.

This supplies the brief's alternative of a concrete convex-body extremal result. It does not supply an improved upper cover from I203. The lower bound is independent of I203 and its pending reviews. There is no claim that this lower bound, or the classical 1/3, is the actual infimum of covering costs.

## The geometric estimate

Center the edge-two tetrahedron at 0. Its volume is 2sqrt(2)/3, its minimum projection area is sqrt(2), and its vertices satisfy |v_i|^2=3/2 and v_i.v_j=-1/2 for i!=j. Define the nonnegative density

    f(x)=(19/10-|x|^2)1_T(x).

Its integral is 16sqrt(2)/15. The new chord calculation proves exactly

    sup over affine lines ell of integral_ell f ds =16sqrt(15)/25.

For a chord with endpoints p,q, length l and midpoint m, its integral for the general density a-|x|^2 is l(a-|m|^2-l^2/12). Nonnegative barycentric endpoint coordinates give |m|^2>=l^2/4-1/2. The resulting cubic is maximized at l=sqrt(a+1/2), when 3/2<=a<=7/2. Chords joining opposite edges attain this value; thus the estimate handles all directions and offsets exactly.

For any actual cylinder C=B+R u, Tonelli bounds its f-mass by (16sqrt(15)/25)|B|. Summing over any finite cover gives the displayed theorem. This applies to arbitrary measurable finite-area bases, including nonconvex or disconnected bases. It is a direct finite-cover lower bound, with no approximation error or omitted boundary. Similarity gives the result for every positive edge length.

Averaging any nonnegative quadratic polynomial over tetrahedral symmetries preserves its mass and does not increase its largest line integral. The average has form alpha+beta|x|^2. Nonnegative beta gives a certificate at most 1/3. For negative beta, normalization reduces to a-|x|^2, a>=3/2. The exact line integral maximum is (2/3)(a+1/2)^(3/2) up to a=7/2 and 2(a-5/6) thereafter. Differentiating their mass ratios proves that a=19/10 is optimal, with normalized value sqrt(15)/9. This is sharpness of a method, not sharpness of the covering problem.

## Two routes and the dependency boundary

The [analytic record](../experiments/i209_elliptic_tetrahedron/analytic-attempt.md) develops both routes in full.

* **Wall-compatible elliptic upper route.** A new mixed field from the radial power p=1/2 is divergence-free, tangent to both wedge walls, elliptic in |b/r|<1/sqrt(3), and hyperbolic near the walls. With fixed apex cutoff d, the record proves inverse labels, complementary caps, closed endpoint coverage and two explicit tip cylinders. Conditional on I203's nonlinear theorem, this is an actual finite cover. Its coefficient-one determinant penalty is a^3(1/d-1/a)/(6sqrt(3)), a=1/2. Exact integration shows its quadratic cost coefficient is positive for every 0<d<=a. Thus this construction does not improve the upper bound, even with I203's better cost. An affine wall-tangent field is necessarily hyperbolic; it cannot provide an elliptic shortcut.
* **Geometric lower route.** The global quadratic-density/chord estimate above succeeds. It raises the regular tetrahedron's lower endpoint above the universal 1/3 and solves the full quadratic-certificate optimization, without invoking the failed upper construction.

I independently multiplied I203's B,G matrices and read the actual accepted square lemma. Its off-diagonal product is (k^2-t^2)/(1+k^2) in [0,1), so the pointwise application is valid, including both endpoints. The full nonlinear statement is still treated as pending, and no live review output was read.

## Importance and limits

Bezdek–Litvak's primary Theorem 3.1 proves the directionwise lower bound 1/3 and hence the absolute minimum-shadow lower bound 1/3 in dimension three. Its ellipsoid proof already uses the density method; that method is not claimed new. The new proposed content is the tetrahedral chord estimate, the resulting exact constant sqrt(15)/9, and the optimal quadratic certificate. The four accepted companions provide upper constructions, including the angular cost 1/2-tau^2/240+(25/2)tau^3 with error at most 2tau^4; none of those paid results is re-counted.

The bound here is for absolute base area divided by the minimum projection area of a regular tetrahedron. It does not automatically extend to directionwise normalized cost or arbitrary affine images. There is no worldwide-priority claim: the [literature note](../sources/i209_elliptic_tetrahedron/literature.md) identifies the primary comparison and the limits of the search. Contribution significance and prior-art sufficiency remain for the independent parent gate.

The [reading/failure log](../experiments/i209_elliptic_tetrahedron/reading-and-failures.md) and [authentication record](../experiments/i209_elliptic_tetrahedron/input-authentication.json) identify the inputs and retained source copies. Only the authorized I209 files and source directory were written. I31 is unchanged. No subordinate agents, research code, scans, numerical experiments, tests, snapshots, seals, staging, commits or publication were used. Detached final output hashes accompany the handoff.
