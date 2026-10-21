# Moving cylindrical exclusion: research calculations, not a frozen theorem

PREFREEZE. One family375. The old r23 energy-free finite-index classification for every 4≤n≤7 is unchanged and unproved here. This note develops a different localization calculation at that full scope; it does not nominate its supporting estimates or change any old disposition.

## Inputs and notation

Let u:R^n→(-1,1), 4≤n≤7, solve Δu=u³−u with finite Morse index. Write e(u)=|∇u|²/2+(1−u²)²/4. Disjoint negative tests show that u is stable outside a fixed B_a in R^n. Set k=7−n and v(x,y)=u(x) on R^n×R^k. The lifted solution is stable for tests supported outside C_a=B_a×R^k, by applying exterior stability to each y-slice and adding |∇_y φ|². It is generally NOT globally stable or finite index. If u has one negative test, broad disjoint translates in y give infinitely many negative tests for v.

Use the source's seven-dimensional normalization M_t(z)=E(v;B_t(z))/(s0 ω6 t^6), K(t)=1+sup_z M_t(z), s0=2√2/3. The classical Modica and energy-monotonicity operations do not require stability. In particular K is nondecreasing, K(t)≤1+Ct, and K(s)≤C(s/t)K(t) for s≥t≥1 by ball covering. If the original centered energy density is unbounded then K(t)→∞: Fubini over |y|≤t and |x|≤t compares E_7(B_{2t}) with c t^k E_n(B_t). All constants may depend on n and the fixed normalization.

For each R choose a center z_c with M_R(z_c)≥K(R)/2 (for K(R) sufficiently large). Translate radial coordinates but retain the physical core cylinder C_a. Put ρ=(R²+|z−z_c|²)^(1/2), L=R/√K(R), θ=.02, A_R=K(R)L^(1−θ), and w(s)=L+log s. Then L≥c√R and w(s)/s→0 uniformly for s≥R.

## 1. A cylinder energy bound that uses the PDE energy, not ambient volume

For w≥1, s≥w, and any center z_c, cover

    B_{Cs}(z_c) ∩ { |x|≤Cw }

by at most C(s/w)^k balls of radius C'w. (If it is empty the assertion is automatic; the original x core stays centered at the origin.) Each energy is at most C K(C'w) w^6. Covering a fixed dilation by boundedly many w-balls gives K(C'w)≤C K(w). Therefore

    E(v; B_{Cs}(z_c) ∩ {|x|≤Cw}) ≤ C K(w) s^k w^(n−1).       (1)

The constants absorb fixed enlargements and a. This is uniform in z_c. The same bound holds for good-interface area in fixed enlargements if the uniform good-chart area-to-energy estimate is available. It is not a claim about arbitrary singular zero-set area. A unit-separated bad net can be bounded by the same energy covering because every zero carries a fixed unit-ball energy lower bound.

On the principal R ball, the fraction of its energy lost by deleting the cylinder of radius Cw(R) is at most

    C [K(w(R))/K(R)] [w(R)/R]^(n−1) = O(K(R)^(-(n−1)/2)).  (2)

Here w(R)/L→1, K(w(R))≤K(R), and constants are fixed before R→∞. In contrast, bounding by ambient volume would give an unnecessary and possibly nonvanishing factor R/K(R)^3 in dimension4. Formula (2) avoids that failure without assuming the desired energy bound.

## 2. Why fourth-order cutoff losses would suffice in every old dimension

Suppose, only for this calculation, that a localized version of the source fourth-moment estimate has on each shell ρ≈s an additional collar allowance

    J4(s) ≤ C K(w(s)) s^k w(s)^(n−5).                        (3)

This is the dimensional size of (1) times w^−4. It is NOT inferred merely by differentiating a cutoff, and is NOT yet a proved PDE estimate in this note.

The source radial curvature payment multiplies a shell fourth moment by ρ^−4 times sup_d W_*(logρ,d)d³. The actual source weight satisfies this supremum ≤C(L+log s)^(3−θ). Thus (3) would give the shell error

    C K(w(s)) s^(k−4) w(s)^(n−2−θ).                        (4)

Write s=2^jR. Since w(s)≤Cs for large R,
K(w(s))≤K(Cs)≤C2^jK(R), and w(s)/L≤C(1+j). Dividing (4) by A_R bounds its dyadic sum, for n≥5, by

    C (L/R)^(n−3) Σ_{j≥0} 2^{(4−n)j}(1+j)^(n−2−θ),       (5)

which tends to zero. The apparent n=4 borderline in this coarse inequality must NOT be discarded. A better bound for K(w(s)) is needed there.

For every n≥4 use instead the ball-covering estimate at scale L:

    K(w(s)) ≤ C [w(s)/L] K(L) ≤ C [w(s)/L] K(R).

Now the sum divided by A_R is at most

    C (L/R)^(n−3) Σ_{j≥0} 2^{(3−n)j}(1+j)^(n−1−θ),       (6)

finite already at n=4 and tending to zero as K(R)^(-(n−3)/2). This completes the scalar shell summation conditional on (3). It uses no lower bound on the rate of divergence of K.

The same bound (4) pays direct radial cutoff Hessians: the primitive F≤Cw^(1−θ), a second derivative of a core cutoff costs w^−2, the radial factor is ρ^−4, and good area is bounded by (1). Thus those terms also have the normalized bound (6), provided the relevant area and contact transfer are justified on the collar. Normal depth buffers logarithmic in ρ fit inside a sufficiently large fixed multiple of w.

The older fixed-core estimate inserted C s^k into the fourth moment and produced R/K(R)^2 in dimension4. Growing the exclusion to w changes the proposed moment loss from C s^k to C K(w)s^k w^(n−5), giving (6). This is a genuine improvement of the scalar bookkeeping, not a proof of (3).

## 3. Capped reach to keep growing windows away from the unstable cylinder

Let r(x)=sqrt(1+|x|²) and fix a large constant A0. On regular zeros outside a large fixed cylinder consider

    d_hat(z)=min{d(z), r(x)/A0},                              (7)

where d is the source's actual penalized reach. On a branch where d_hat=d, its defining chord length is at most d_hat because Γ≥1. Thus both the source and receiving foot remain away from C_a once r is large, with a fixed fractional margin. The source's density-window proof uses only the chord confinement inequality and monotonicity, so it can be run at a lower available length d_hat≤d. Its window h=d_hat exp(−C sqrt(log(K(d_hat)+1))) is ≤d_hat≤r/A0. A local stable-ball regularity theorem would then isolate the graph inside the exterior stable region. The actual source corollary is stated for entire stable solutions; this localization must be taken from a valid local primary theorem or its proof, not inferred from its name.

At a cap branch, ambient |∇r|≤1, |D²r|≤C/r, and the surface Laplacian identity gives

    Δ_Σ(r/A0) ≤ C/(A0 r) + |H|/A0.                        (8)

The minimum of two locally semiconcave functions is locally semiconcave; at a switch its singular Laplacian part is nonpositive. Consequently the source's decreasing primitive F has a favorable singular part even for (7). However cap branches are artificial branches, not contacts, so their smooth contribution (8) must be paid separately.

If a core cutoff is supported where r≥A1 w(ρ), with A1/A0 sufficiently large, cap branches have d_hat≥(A1/A0)w. The actual radial weight there has an exponentially small tail after choosing A1/A0 above its fixed truncation constant. The growth multiplier f(d_hat) likewise has an eventual exponential tail. This identifies a plausible payment for cap branches; a uniform weighted proof for all derivative, receiving-foot, and defect-comparison terms has NOT been completed.

Changing E=e^(−κd) to E_hat=e^(−κd_hat) is not an identity: E_hat≥E, and the extra e^(−κr/A0) must be explicitly included. A foot on a genuine branch obeys d_hat(y)≤d(y)≤d(z)=d_hat(z), so the direction of the source's monotone-weight transfer survives on that branch. No foot is invented for a cap branch.

## 4. The exact operation not yet paid

The remaining requirement is a localized, capped-reach analogue of source Proposition growth-fourth-order and its compatible radial gluing/transfer. It must provide (3), plus the usual CK(s)s² term, uniformly as the center moves and as the outer radius B→∞ at fixed R. It must control bad nets, D², curvature a⁴ and E_hat² simultaneously, with constants fixed before R→∞.

One cannot obtain this from the stated M1 just by multiplying its conclusion by a core cutoff: M1 assumes global stability. Nor does the inequality Q_v(F)≥−C∫_{C_a}F² supply it. The actual proof uses all of the following linked operations:

- L11 is a nonlocal weighted comparison using an exponentially decaying convolution and the weight-ratio bound χ(z)≤e^{|z−w|/R}χ(w). A cutoff that vanishes on the core does not satisfy this bound.
- Growth gluing lifts profiles along normal immersions, with possible multiplicity. Putting a cutoff only at the base does not guarantee that the physical test avoids the core. Putting it only in physical space changes the base weights after normal integration.
- The growth multiplier transfers a positive mean-curvature charge from source to receiving foot and relies on near-equality of exponential spatial weights for d≤sqrt(R). A vanishing core cutoff needs an additive derivative-error estimate, not a ratio at a zero denominator.
- The curvature and defect closure must turn those extra inverse-square errors into inverse-fourth errors by Young absorption while keeping the same powers of the cutoff. Without this step the calculation (6) has no PDE premise.
- The radial construction has a different interpolation of sheet amplitudes. Both the source and receiving feet must have the required clean windows, and all cutoff mismatch terms must be paid without changing the numerical reserve .73/.895 and the subsequent radial coefficient comparison.

A promising design is a smooth cutoff of |x|/(A1 w(ρ)), raised to a sufficiently high fixed power, combined with an enlarged collar to pay exponential-kernel leakage and long normal rays. Basic derivative bounds are O(w^−1) and O(w^−2), but those bounds alone do not prove the coupled estimate. The positive numerical margins make small losses conceivable; they do not authorize them without quantitative estimates.

## Disposition at this checkpoint

No full feasibility closure, no freeze, no independent grades. The moving-core covering and shell calculation remove a specific earlier scalar obstruction. The remaining coupled localization has not been proved. The old full 4–7 target remains unchanged; no 5–7 restriction, symmetry condition, bounded-density substitute, conditional bridge, or supporting bound is nominated.
