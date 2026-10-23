# Prefreeze calculations IV: extend over a power-sized normal neighborhood

This continues the actual non-lc resolved construction, before removal of the cover. It pays a neighborhood of the PUNCTURED zero fiber, including nearby nonzero values. It does not pay an ambient neighborhood of the origin, and is not a restricted nominee. The full question in note00 remains unchanged.

## 1. Polynomial derivative bounds for the actual zero map

The smooth resolved transport has bounded derivatives of every fixed order on compact tubes. The analytic resolution b is an immersion off E, with inverse onto the smooth punctured zero family. Let kappa be its smallest singular value in local analytic charts, using the total map including the base coordinate. This is a continuous subanalytic function, positive off E. Its zero set is contained in E. On compact chart blocks, the same distance inequality read in Bierstone–Milman gives

    kappa(p) >= c dist(p,E)^N.

Because the spatial component of b vanishes on E and has bounded derivatives,

    |b_spatial(p)| <= C dist(p,E).

Consequently kappa(p)>=c' |b_spatial(p)|^N. The derivative of the inverse immersion is at most kappa^(-1), and its higher derivatives follow by differentiating the inverse equations. Every fixed order has only a finite inverse power of |x|. Finite charts and smaller compact tubes make constants uniform in u. The same argument applies to b_0 and to the total resolution. These are derivatives along the smooth zero manifolds, with their induced Euclidean metrics; curvature terms arising from charts also have finite power bounds by the analytic equations.

It follows that the zero map z_u from note02, and its inverse, have finite power derivative bounds of every fixed order off the section. The pair-quotient argument already gives, for some a>0,

    c |y|^(1/a) <= |z_u(y)| <= C |y|^a.                            (1)

Thus we have stronger data than an arbitrary intrinsic Hölder homeomorphism: a smooth isotopy away from the section, polynomially controlled derivatives, and bilateral radial powers.

## 2. Relative analytic normal coordinates with a power-sized domain

Put X_u={G(·,u)=0}. At y in X_u\{0}, define

    n_u(y)=overline(d_xG(y,u))/||d_xG(y,u)||^2.

The function of one complex variable v,

    v -> G(y+v n_u(y),u),

has derivative1 at v=0. Solve it for v=nu_u(y,c), and set

    tau_u(y,c)=y+nu_u(y,c)n_u(y),
    G(tau_u(y,c),u)=c,  tau_u(y,0)=y.                              (2)

These are real analytic relative normal coordinates off the section. Here is why a FINITE POWER domain is available, rather than a radius selected independently at every point. On each compact annulus r<=|y|<=2r and a compact smaller parameter disk, the relative normal map is an immersion along its zero section and injective on a sufficiently small normal neighborhood. Uniform injectivity follows by compactness and the local inverse function theorem: a sequence of collisions at normal size tending to zero would limit to a point on the zero section, contradicting local invertibility. Use larger annuli to avoid artificial boundary effects.

The analytic normal map and the collision/critical-point conditions are subanalytic on compact annular representatives. Taking the infimum of admissible normal radii is a bounded subanalytic minimization; the graph is obtained by proper projections and their complements. It is positive for r>0. The one-variable lower-arc argument in the proof of Bierstone–Milman6.4 bounds it below by c r^N after decreasing r. Equivalently apply that distance inequality to the compact graph completed at r=0. This controls both collision radius and the inverse-function radius uniformly in u. No assertion about a subanalytic FLOW is needed.

The analytic gradient, its first few derivatives, and inverse Jacobian matrices obey analogous finite power bounds on the smaller normal neighborhood. Increase an integer m as needed so that

    |c| < epsilon |y|^m                                           (3)

lies in that neighborhood and

    |tau_u(y,c)-y| < |y|/4.                                       (4)

For example, if ||n||<=C r^(-q), the one-variable Taylor error is O(|v|^2 r^(-2q)); taking |v| much smaller than r^(2q) pays the scalar inverse-function estimate. Increasing m also keeps the physical normal displacement within the polynomial injectivity radius. Derivatives of tau and its inverse, to each fixed finite order, are bounded by finite inverse powers of r. All these statements concern nested annuli/compact representatives and the full parameter family, not just a single smooth point.

## 3. Explicit function-preserving extension on a thinner neighborhood

Choose an integer M>m/a, with extra margin, and epsilon small. For

    x=tau_0(y,c),  |c|<epsilon |y|^M,

define

    T_u(x)=tau_u(z_u(y),c).                                       (5)

By (1), |z_u(y)|>=c_0 |y|^(1/a), so M>m/a makes the target normal chart valid uniformly. Use a wide neighborhood with 4epsilon in the formula and an inner one with epsilon for estimates. Equation(5) is explicit, preserves the defining FUNCTION exactly, agrees with z_u on c=0, and is the identity at u=0. It is a diffeomorphism onto its image off the section. Its inverse on that image is

    tau_0(z_u^(-1)(y'),c),  where tau_u(y',c)=x'.                   (6)

The spatial radii of x and y are comparable by(4), as are those of T_u(x) and z_u(y). Hence (1) supplies bilateral radial power estimates for T. The chain rule, the polynomial derivative estimates for z and tau, and the lower bound in(1) supply polynomial growth for derivatives of T and its inverse off the section. This controls variation in u as well, on the covered disk.

For clarity about two-point estimates on a nonconvex domain, a derivative bound alone is not enough. The inner neighborhood has a buffer inside the wide one. The defining chart quantities |c|/|y|^M and their derivatives have polynomial growth, so a Euclidean ball of radius c r^K about each inner point lies in the wide neighborhood, for some fixed K. The same holds on the target, using (6) to express its defining inequality. Shrink the outer spatial and parameter representatives to avoid their boundaries.

For points of separation d<c r^K, their straight segment lies in the wide domain and the derivative estimate gives C d r^(-b). Independently, the radial bound gives C r^a when d<r/2. Optimize as in note03 to obtain C d^(a/(a+b)). For d>=c r^K but d<r/2, radial control gives C d^(a/K); for d>=r/2 use C d^a. Thus a positive exponent

    gamma <= min(a, a/K, a/(a+b))                                 (7)

works on the inner neighborhood, and similarly for the inverse using its own exponents. This gives genuine two-point Hölder estimates there, including the parameter coordinate and continuity at the adjoined origin section. Exponents are existential and depend on the family, charts, resolution and chosen compact domains.

The construction uses classical analytic separation and tubular coordinates. Even if all its estimates are retained, it is not by itself a substantial full-scope result: it omits an entire portion of every ambient neighborhood.

## 4. The part still absent and the cover issue

The set defined by(3) or its thinner version is a neighborhood of each punctured zero point, but after adjoining the origin it need NOT contain any ambient ball. Points with |G(x,u)| comparable to a low power of |x| can lie outside it at arbitrarily small radius. These are actual portions of the nearby Milnor levels, not points that can be discarded by shrinking a germ. Formula(5) gives no map on that remaining region.

An arbitrary extension there by Section13's smooth kernel fields restores the qualitative theorem, but note04 shows precisely that it can destroy every inverse Hölder exponent even when it agrees with the prescribed zero map. The gradient-collapse construction of note03 describes the missing region and its attaching maps, but its available variational estimate is exponential in an inverse power of the value. It does not supply the needed power bound for completing(5).

There is also a domain qualification. Unlike the source's complete tube maps, the images of the thin neighborhoods in(5) may differ for u and zeta*u. Thus the source's exact-domain seam formula cannot simply be asserted on these incomplete neighborhoods. The zero-set maps had exact common domains, so their descent in note02 remains valid. If the full ambient extension on common tubes with a positive exponent were constructed, that same quantitative seam calculation would apply immediately. We do not treat the thin-neighborhood map as if this full interface had already been closed.

The outstanding task is therefore a controlled completion across the remaining parts of the Milnor levels, compatible with the actual function values and the prescribed normal-neighborhood map, or another construction that gives the same entire ambient estimates. The classical zero-resolution and normal-extension operations substantially narrow it; they do not eliminate it. No claim of exhaustion, impossibility or an invariant obstruction follows.
