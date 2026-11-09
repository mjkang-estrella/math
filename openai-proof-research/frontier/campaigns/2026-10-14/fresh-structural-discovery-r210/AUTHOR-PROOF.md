# Author proof for the exact frozen r210 target

This is a discovery-stage author proof, not an independent correctness or contribution decision. The target is exactly FROZEN-STATEMENT.md, SHA256 cd65e255f9fdb798bb38fd5e3291f2f657e7dae91c0af62fdf366e05ec075295. No assertion concerning finite-regularity immersions is made. All constructions are existential; the potentially very large finite collections below need not be enumerated computationally.

## 1. Conventions and paid interfaces

Put D=(-1,1)^2 with coordinates (X,Y). Vector and matrix norms without a metric subscript are Euclidean norms and Euclidean operator norms. For a function or tensor, its C^m norm is the maximum, over coordinate partial derivatives of order at most m, of the component supremum norms (or any fixed equivalent matrix norm). Constants converting component norms are included in the displayed construction budgets. All compactly supported functions used below are extended by zero. Balls and distances used to place supports are Euclidean.

We use the following entire Source334 interface at the stipulated pin, without auditing it. Fix S=[-3,3]^2, P=[-1/10,1/10]^2 and the source's smooth even h: h=1 on [-1/2,1/2], h decreases on the positive half-axis, h>0 for |y|<1, h<0 for |y|>1, h(1)=0 and h'(1)<0. If a smooth positive metric g0 near S has

    K_g0(x,y)=kappa (x^2-h(y)),   kappa>0,

then arbitrarily small smooth symmetric perturbations eta supported in P may be chosen so that g0+eta stays positive, has K<-kappa/2 on [-1/5,1/5]^2, and admits no smooth z near S satisfying throughout S

    det H = K det(g) (1-|dz|_g^2),
    1-|dz|_g^2 > 0,  H_yy != 0,  |H_xy/H_yy| <= 1/100,
    H=Hess_g z.

“Arbitrarily small” means in any specified finite collection of C^m seminorms, for this fixed background and fixed kappa. The source's Proposition prop:patch proves more, namely residuality in its fixed-exterior metric slice. No uniformity as kappa tends to zero is used here.

The source proves this through its full cap regularity proposition, hyperbolic propagation and metric-level pulse argument. Its differentiated curvature identity is Dq-P_zx q-P_zy=K_y G+O(K), with D=partial_x-q partial_y and G=det(g)(1-|dz|_g^2)/H_yy^2. Its high derivative equation has transverse drift (l+1) A_s+O_l(A). The free-edge multiplier and auxiliary elliptic estimate supply the all-order endpoint data. A change only in the theta-theta metric coefficient produces the principal curvature-density forcing -1/2 partial_xi^2(delta g_theta,theta). The resulting forced moment is of size delta tau^(1-N), whereas the competing spatial moment is of size delta^2 tau^(1-N). All those operations are paid dependencies, not r210 contributions.

We also use the classical smooth local realization interfaces:

* a smooth surface metric with K(q) nonzero has a smooth local isometric embedding in R3;
* a smooth surface metric with K(q)=0 and dK(q) nonzero has a smooth local isometric embedding in R3.

The actual Nakamura–Maeda 1986 research-report version states these as Theorems A and C and supplies the real-principal-type construction and Nash–Moser proof. Its clean-sign calculation uses K as one coordinate and a characteristic polynomial with a nonzero base derivative at its degenerate characteristic; this is an existence theorem for a new smooth map on a neighborhood, not regularity improvement of an arbitrary finite-regularity immersion. The theorem supplies exactly the pointwise existence used in Section 8 below. No common neighborhood, common map, or uniform estimates across different points are required. The published 1989 endpoint was inaccessible (HTTP 403); the read version and its exact extents are recorded separately.

## 2. Quantitative boundary detection in a fixed coordinate disk

Let c in D, M>=1, 0<r<=1/(1000M), and suppose B(c,4r) is contained in D. Let g be any smooth metric there with

    (1/2) I <= g <= 2 I.

Suppose K_g<0 on Delta=B(c,r), K_g=0 on its boundary, and K_g=-a on B(c,r/2), where a>0. Suppose F is a smooth isometric immersion on a neighborhood of the closed ball B(c,4r) and

    |partial^alpha F| <= M  for |alpha|=2,3

on that ball. The same argument applies when F is defined on a larger open set containing the ball. This is a bounded class of smooth immersions, not the class of all C^3 immersions.

Define n=(F_X cross F_Y)/|F_X cross F_Y|, e=n(c), z=<F,e>, nu=<n,e>, and H=Hess_g z. The Gauss formula gives H=nu II, where II_ij=<F_ij,n>, and

    |dz|_g^2 + nu^2 = 1.

Because |F_X|,|F_Y|<=sqrt(2) and |F_X cross F_Y|=sqrt(det g)>=1/2, each coordinate derivative of n has length at most 4 sqrt(2) M<6M. Integration along straight line segments in B(c,4r) gives |n(x)-n(c)|<=9M|x-c|<=36Mr<=0.036. In particular nu>0 and |dz|_g<=1/2 throughout the ball. Also |II_ij|<=M and

    |partial_k H_ij| <= M+12 M^2 <= 13 M^2.

It follows, again on straight segments, that

    ||H(x)-H(y)||_op <= 100 M^2 |x-y|.                 (2.1)

Here H is written in the fixed (X,Y) coordinate frame. The constants are independent of all derivatives of g; the isometry and the bounds on F give them directly.

For completeness, the boundary identity used next is derived, not assumed from a nonsolvability claim. Raise indices with g and put

    T^{ij}=(Delta_g z) g^{ij}-H^{ij}.

In dimension two this is the cofactor of the Hessian as a metric endomorphism. Commutation of three covariant derivatives of z gives

    nabla_i T^{ij}=-K_g z^j.

Consequently the Darboux equation for an actual height yields

    div_g(T dz)=T^{ij}H_ij-K_g|dz|_g^2
               =2 det(g^{-1}H)-K_g|dz|_g^2
               =K_g(2-3|dz|_g^2).                    (2.2)

This is the coordinate-invariant form of Khuri2009's equations (6)–(8). Only third derivatives of z enter its pointwise derivation; F here is smooth. The divergence theorem on the smooth disk gives

    integral_Delta K_g(2-3|dz|_g^2) dV_g
      = integral_boundaryDelta T^{ij} z_j mu_i dS_g,  (2.3)

where mu is the outward g-unit conormal. Since the left integrand is negative and 2-3|dz|_g^2>=1, its absolute integral is at least pi a r^2/8: use K=-a on the radius-r/2 disk and sqrt(det g)>=1/2.

Write H*=max_boundaryDelta ||H||_op. Since ||g^{-1}||<=2, ||T||_op<=12H*. Also |dz|<=sqrt(2)/2 and |mu|<=sqrt(2), so the absolute boundary integrand is at most 12H*. The g-length of the circle is at most 2 pi sqrt(2) r<9r. Hence

    H* >= pi a r/864 > a r/1000.                     (2.4)

At a boundary point b attaining H*, the Gauss equation and nu>0 show that H(b) has determinant zero. It is nonzero by (2.4), so it has rank one. Set

    h0 = a r/1000,     sigma = h0/(10^6 M^2).        (2.5)

For the applications we take a<=1, so sigma is much smaller than r.

## 3. Finite capture of every bounded smooth immersion

Choose once and for all a finite net R_1,...,R_J of plane rotations whose first-axis lines are within 1/1000 radian of every unoriented line. Choose a finite sigma/10-net b_1,...,b_L on the circle of radius r. For each pair (i,j), choose a distinct center c_ij strictly outside the disk, within sigma/3 of b_i. The centers can all be chosen in the collar 0<|x-c|-r<r/20: there are only finitely many choices to make, and each allowed set contains an open set.

Choose positive scales lambda_ij so small that the rotated images

    Phi_ij([-4,4]^2),  Phi_ij(x,y)=c_ij+lambda_ij R_j(x,y),

have pairwise disjoint closures, lie outside the closed disk, lie in ||x-c|-r|<r/10 and B(c,2r), and every point of each such image is within sigma/2 of b_i. For example, after the finitely many centers have been fixed, take each scale smaller than a suitable fixed multiple of the minimum of all center separations, distances to the closed disk and collar edges, and sigma. All these minima are positive. The placements depend on r,a,M, but not on the future metric's collar slope or its patch curvature amplitudes.

For the point b from Section 2, take i with |b-b_i|<=sigma/10 and take j whose first axis approximates the kernel of H(b). In that frame a rank-one symmetric matrix is lambda v v^T with |lambda|=||H(b)||>=h0; therefore

    |H_yy(b)| >= h0 cos^2(1/1000),
    |H_xy(b)/H_yy(b)| <= tan(1/1000).

Every point x in the selected full patch satisfies |x-b|<sigma. Equation (2.1) and (2.5) bound the matrix change by h0/10000. Thus H_yy stays nonzero and |H_xy/H_yy|<1/100 throughout that patch. Moreover |dz|_g<=1/2 there.

Pullback by Phi_ij preserves the Darboux equation and the intrinsic gradient norm; its common dilation multiplies all Hessian entries in the rotated frame by lambda_ij^2, so it preserves their ratio. If this patch has a Source334-obstructed pullback metric, z composed with Phi_ij is a prohibited smooth admissible height. Therefore no smooth immersion with the indicated coordinate second- and third-derivative bound M exists on the whole ball.

This is a finite construction for one bounded smooth class. It does not assert that the ball has any bad point. It can in fact be locally immersible at every point, as will occur in each block below. The eventual bad points arise only from accumulation of blocks whose bounds M tend to infinity.

## 4. Curvature profiles with independent interior mass and boundary slope

Fix a block B(c,4r), an integer m>=0, a derivative budget epsilon>0 and a bound M>=1, with r<=1/(1000M). Fix a radial cutoff beta equal to 1 on B(c,2r) and zero outside B(c,3r), 0<=beta<=1. Let T>=1 be a bound for multiplication by beta in C^m, obtained from Leibniz's rule and its finitely many derivatives.

We construct a smooth profile k on the ball, equal to a positive constant a outside B(c,2r), with:

* k<0 inside B(c,r), k=-a on B(c,r/2), and k=0 on the circle with nonzero normal derivative;
* the finite patches of Section 3, with k composed with Phi_p equal to kappa_p(x^2-h(y)) on a neighborhood of S, where each kappa_p>0;
* every zero of k is regular; k is positive outside the negative disk and the negative components inside the model patches;
* ||beta k||_{C^m}<epsilon/2.

Here and below p ranges over the finite set of patches in this block. First choose a>0, a<=1, small enough to pay the C^m norm of a fixed radial core and outer profile at scale r. This choice is made before the finite placement, which uses this a in (2.5).

Here are precise parameter dependencies. Smooth radial interpolation, using cutoffs at fixed fractions of r, gives functions k_{a,b} such that

    k_{a,b}=-a for rho<=r/2,
    k_{a,b}=b(rho-r) for 9r/10<=rho<=11r/10,
    k_{a,b}=a for rho>=3r/2,

where rho=|x-c| and 0<b<=a/r. Interpolate between two negative functions in r/2<rho<9r/10 and between two positive functions in 11r/10<rho<3r/2. Smooth cutoffs constant near the joining radii give exact agreement on neighborhoods of those radii. The function is constant near c, so the nonsmoothness of rho at c is irrelevant. For each j<=m,

    ||k_{a,b}||_{C^j(B(c,4r))}
      <= C_j(r) a,                                 (4.1)

uniformly in 0<b<=a/r; one may take C_j(r) a bounded by a fixed multiple of a times max(1,r^{-j}). The only zero is initially rho=r, with radial derivative b. Take a so small that T C_m'(r) a<epsilon/4, where C_m' bounds all j<=m.

Now make the finite placement of Section 3. Take a fixed model cutoff chi_p equal to 1 on a neighborhood of S and supported in (-4,4)^2, and let chi_p^phys=chi_p composed with Phi_p^{-1}. Replace k_{a,b} on each patch by

    (1-chi_p^phys) k_{a,b}
      + chi_p^phys kappa_p ((x^2-h(y)) composed with Phi_p^{-1}).  (4.2)

Arrange that chi_p starts transitioning only outside S. There x^2-h(y)>0, because either |x|>=3 or |y|>=3. The old curvature is also positive, since the patch is outside the disk. Thus the transition is strictly positive. Inside S, zeros of x^2-h(y) are regular: its gradient is (2x,-h'(y)); at a zero with x=0 one has y=+/-1 and h'(y) nonzero. No new zero is created in the transition.

On every patch the old profile is exactly b(rho-r). For its fixed geometry and every j<=m, the C^j norm of its correction in (4.2) is at most

    C_{p,j} b + D_{p,j} kappa_p,                    (4.3)

where these finite constants include all cutoff, scale and rotation costs. For example a model derivative of order j has cost bounded by a model constant times lambda_p^{-j}; differentiating the cutoff times rho-r has only fixed finite costs once lambda_p,r,c_p are fixed. There are finitely many pairs (p,j). Choose b>0 sufficiently small, then all kappa_p>0 sufficiently small, so that the sum of the corrections' C^m norms is less than epsilon/(4T). They may be chosen independently small; neither appears in the mass a used to locate the patches. Combining this with (4.1) proves the final norm budget.

All patches stay a positive distance from the disk, so the disk profile and its nonzero boundary slope are unchanged. This construction resolves the scale dependence explicitly: choose r,M,epsilon,beta; then the interior amplitude a; then the finite net and its patch scales; then the slope b and the patch amplitudes kappa_p. No smallness restriction on a is imposed after the scales depending on a have been chosen.

## 5. Disjoint blocks approaching an arbitrary closed nowhere-dense set

Let C be a nonempty relatively closed nowhere-dense subset of D. Put E=D\C. We claim there are closed balls B_n=closed B(c_n,4r_n) contained in E, with pairwise disjoint closures, such that:

    M_n=n+1,  r_n<min(2^{-n},1/(1000M_n)),
    dist(c_n,C)<2^{-n},

and every p in C is a limit of a subsequence of centers. The family is locally finite in E.

To see this, take a countable basis of open balls whose closures are compact in D, and schedule each basis ball meeting C infinitely often. At stage n choose a point of C in the scheduled ball. The finitely many previous closed balls avoid C, so a sufficiently small neighborhood of this point avoids all of them. Since C has empty interior, that neighborhood contains a point c_n of E, still inside the scheduled ball and within 2^{-n} of C. Its distance to C and to the complement of D is positive. Choose r_n>0 small enough for all stated bounds, for B_n to stay in that neighborhood and E, and for 4r_n<dist(c_n,C)/2. This gives the induction. Repeated scheduling of arbitrarily small basis neighborhoods proves the subsequence assertion.

For any compact Q subset E, dist(Q,C)>0 (relative closedness and Q compactly inside D suffice). The distances of all points of B_n from C tend to zero. Thus only finitely many B_n meet Q, proving local finiteness. No assertion that the centers are dense in D is needed.

Apply Section 4 on block n with m=n and epsilon_n=2^{-n-20}. Obtain beta_n, k_n, its disk amplitude a_n, collar slope b_n, and finitely many model patches. Their zero sets are regular, and

    ||beta_n k_n||_{C^n}<epsilon_n/2.                (5.1)

Let T_n>=1 bound multiplication by beta_n in C^n and set gamma_n=epsilon_n/(2T_n).

We need a smooth positive background k_+ on E, flat on C, satisfying

    ||k_+||_infinity <= 2^{-20},
    ||k_+||_{C^n(B_n)} <= gamma_n.                 (5.2)

Here is an explicit existence argument including all accumulations. Choose nonnegative smooth compactly supported bumps phi_j in E whose positivity sets cover E. Each compact support meets only finitely many B_n. Choose coefficients t_j>0 so small that:

    ||t_j phi_j||_{C^l} <= 2^{-j-20}   (0<=l<=j),
    ||t_j phi_j||_{C^l} <= 2^{-j} gamma_n
      (0<=l<=n, for every B_n meeting supp(phi_j)).

There are finitely many constraints at each j. The series k_+=sum_j t_j phi_j converges with every derivative, using its uniformly summable tail for each fixed order. It is smooth on R2 when all summands are extended by zero, positive throughout E, and every derivative is zero on C. The latter follows by evaluating the uniformly convergent derivative series, every summand of which is zero near each point of C. The second family of inequalities proves (5.2) after summing 2^{-j} over the relevant terms. This also proves smoothness at all accumulation points, including sets C of positive measure.

Define

    K0 = k_+ + sum_n beta_n (k_n-k_+).              (5.3)

By (5.1), (5.2) and the multiplication bound, each summand has C^n norm less than epsilon_n. Each is supported in B_n and vanishes near C. For every derivative order m, the terms n>=m form a uniformly summable derivative series; the finitely many earlier terms are smooth. Hence K0 is smooth, with all jets zero at every point of C. Its supremum norm is less than 2^{-19}<10^{-3}.

Inside B(c_n,2r_n), K0=k_n. In the beta_n transition region both k_n=a_n and k_+ are positive, so their convex combination is positive. Away from the blocks, K0=k_+>0 on E. Thus the only zeros in E are the disk circles and the model zero curves, and they are all regular. No unidentified zero arises at a cutoff boundary or block accumulation point in E, since blocks are locally finite there. At points of C the zero is flat, as required.

## 6. Realizing K0 intrinsically and installing the source obstructions

Solve, on D,

    f_XX=-K0 f,  f(0,Y)=1,  f_X(0,Y)=0.

Smooth ODE dependence gives f smooth. On each horizontal segment from 0 to X, the integral equation gives sup|f-1|<=10^{-3} sup|f|, whence sup|f|<=1/(1-10^{-3}) and |f-1|<0.002. Therefore

    gbar=dX^2+f(X,Y)^2 dY^2

is positive and uniformly close to I. Its curvature is exactly -f_XX/f=K0, also when f depends on Y. This is the paid prescribed-curvature ODE of Source334 and Khuri2009.

Enumerate all the model patches from all blocks as Phi_p, p=1,2,..., finitely many in each block. Their full closures are pairwise disjoint and each avoids C. On its model square the pullback

    g0,p=Phi_p^*gbar

has curvature kappa_p(x^2-h(y)). Curvature is a scalar under pullback; the factor lambda_p^2 in the coefficient matrix does not multiply this scalar. Apply the paid patch obstruction separately to each g0,p. Choose eta_p supported in P so that the perturbed pullback has no admissible smooth height, retains the source's central negative-curvature bound, and its pushforward eta_hat_p satisfies

    ||eta_hat_p||_{C^m} <= 2^{-p-10}    (0<=m<=p).   (6.1)

This is possible because

    eta_hat_p = lambda_p^{-2} R_p
                  (eta_p composed with Phi_p^{-1}) R_p^T,
    ||D^m eta_hat_p|| <= C_m lambda_p^{-m-2} ||D^m eta_p||,

and only finitely many seminorms are imposed at this stage. The scaling constants are fixed before the perturbation is chosen. No uniform cap estimate across different tiny kappa_p is required.

Set

    g=gbar+sum_p eta_hat_p.                         (6.2)

Every derivative series converges uniformly in its tail, as in Section 5. Thus g is smooth at all points of D, including every point of C. The total zeroth-order perturbation can, with the fixed component/operator-norm conversion included in (6.1), be made at most 1/8. The above bound on f then gives (1/2)I<=g<=2I on D. This is an estimate on one fixed metric, not on a varying family of candidate immersions.

Each source patch survives exactly: all other tensor perturbations vanish there. All tensors vanish on a neighborhood of each closed disk, because there are only finitely many patches in its block and the other blocks have disjoint closed supports. Therefore K_g equals the prescribed negative profile on each disk and is zero on its boundary, with K_g=-a_n on its half-radius core.

The only places where curvature changes from K0 are the central perturbation boxes. On each such box K0 was strictly negative and the source choice keeps K_g strictly negative. Outside those boxes, g=gbar. Thus K_g^{-1}(0)=K0^{-1}(0). Every zero in E has a neighborhood unaffected by all perturbations, and hence is regular. All derivatives of sum_p eta_hat_p vanish on C, since each summand does and the derivative series converge uniformly. Curvature and its derivatives are smooth finite-jet expressions in a positive metric, so every jet of K_g at C equals the corresponding jet of K0, namely zero.

If 0 belongs to C, all jets of K0 vanish at 0. The ODE initial conditions show that partial_X^a partial_Y^b(f-1)(0)=0 for a=0,1. For a>=2, differentiate f_XX=-K0 f; every Leibniz term contains a derivative of K0 at 0, so the same conclusion follows. Thus gbar-I is flat at 0. Equation (6.1) shows that the tensor sum is flat there as well. This proves the frozen metric-jet assertion at 0, without asserting Euclidean jets at arbitrary points of C.

## 7. Nonimmersion at every point of C

Fix p in C and suppose a smooth isometric immersion F exists on an open neighborhood U of p. Choose a smaller closed coordinate ball about p contained in U. Its second and third coordinate derivatives are bounded by some finite M. By Section 5 there is a subsequence c_n tending to p with n tending to infinity. Since r_n tends to zero, for all sufficiently large indices in that subsequence the entire B_n lies in the smaller ball and M_n=n+1>=M.

On such a block the final metric meets the hypotheses of Sections 2 and 3 with r=r_n, a=a_n and bound M_n. The original finite net was chosen with exactly these parameters. The quantitative cofactor identity finds a rank-one boundary Hessian of size at least a_n r_n/1000. Its coordinate modulus of continuity forces the height in the fixed ambient direction e=n(c_n) to satisfy the source's strict admissibility inequalities on one full oriented patch. By Section 6 that patch admits no such smooth height. This is a contradiction.

Thus p belongs to B(g). The argument works for each p separately; it does not infer obstruction from a limit of obstructed metrics. Nor does it require one block to obstruct all smooth immersions: its assigned bound M_n is sufficient for the fixed hypothetical immersion once n is large. Therefore C is contained in B(g).

## 8. Local realization off C, and the empty-set case

If q is in E and K_g(q) is nonzero, apply the classical nonzero-curvature smooth local existence theorem. If q is in E and K_g(q)=0, Section 6 gives dK_g(q) nonzero, so apply the classical clean-sign smooth local existence theorem. In either case there is a smooth local isometric immersion on some neighborhood of q. This proves B(g) is contained in C, including every transition point and every model-patch boundary. Together with Section 7, B(g)=C.

If C is empty, take a sufficiently small constant epsilon>0 and

    g=dX^2+cos^2(sqrt(epsilon) X)dY^2.

It has constant positive curvature epsilon and satisfies the coefficient bounds. The nonzero-curvature theorem gives B(g)=empty. The flatness and zero-regularity assertions are vacuous, as is the metric-jet assertion conditional on 0 in C.

## 9. Necessity of closedness and empty interior

For any smooth positive metric, the complement of B(g) is open: a local immersion on U works at each point of U. Hence B(g) is relatively closed. The nonzero-curvature theorem gives B(g) contained in {K_g=0}.

If B(g) contained a nonempty open set V, the curvature would vanish identically on V. On a sufficiently small simply connected neighborhood in V choose a smooth oriented orthonormal coframe. Its connection one-form has exterior derivative equal, up to the fixed sign convention, to K_g times the area form, hence is closed. Integrate it and rotate the coframe by the resulting angle; the rotated coframe consists of closed one-forms. Their local primitives are two coordinates whose differentials give g=du^2+dv^2. The map (u,v,0) is a smooth local isometric immersion, a contradiction. Thus B(g) has empty interior. Since it is relatively closed, it is nowhere dense.

This proves the entire frozen scope, conditional only on the explicitly identified paid source and classical existence interfaces. No finite-regularity nonimmersion theorem, stability assertion, or genericity assertion has been proved or used.

## 10. Strongest reduction and limits of the author claim

The source's scalar obstruction and all its cap/pulse estimates are paid. The curvature-prescription ODE, summable derivative tails, flat-jet argument at 0, rotation of a rank-one form and pointwise classical existence are also paid operations. Khuri2009 already derives the cofactor-divergence identity; Nadirashvili–Yuan2002 already uses negative disks, orientation arrangements and accumulation, and its Section 3 uses a compactness/perturbation norm strategy for a stronger claimed sign-restricted example. The later published Nadirashvili–Yuan2008 explicitly gives a lower-regularity metric and leaves the arbitrary smooth problem open; the discrepancy is not resolved here and is not used as novelty evidence.

The operation supplied here is finite capture of a bounded smooth immersion class, with a quantitative boundary-Hessian lower bound and a two-amplitude curvature profile. Separating the disk's interior mass from its independently tiny nonzero boundary slope removes the internal infinite boundary accumulations while keeping every zero outside C regular. This permits the classical existence theorem to prove the reverse inclusion B(g) subset C, which direct disjoint insertion of the source germ does not provide. No compactness limit of immersions, regularity bootstrapping of a C^k limit, stability of an obstructed metric, or preservation of arbitrary source exteriors under perturbation is invoked.

This is an author-proof nomination for separate review. It makes no worldwide-priority, correctness-grade, substantial-contribution-grade, acceptance or campaign-count assertion. The original r22 note's density result is not nominated or renamed; its exact-locus question was not a frozen theorem, and the new proof addresses the missing reverse inclusion by the finite construction above. Excluded history remains excluded and cannot be used to claim exhaustive clearance.
