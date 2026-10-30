# Author proof of the frozen r221 statement

The statement is exactly FROZEN.md, SHA256 `0031fe7106971855b2c1b98e3e1bc40574ed249ad8b17e9ac028d1f30bfae1ce`. It was frozen before this proof was drafted. This is a discovery author proof, not an independent review, manuscript or formalization. Source345 and all its operative upstream inputs are stipulated true. Coefficients throughout are F_2.

## 1. Uniform inputs on a box of metrics

Fix a smooth reference metric h on S^n. A compact C^0-continuous family of positive definite metrics lies in a box

    u^2 h <= g <= v^2 h,       0<u<=v<infinity.                 (1)

Indeed the least and greatest eigenvalues relative to h are continuous on the compact product P x S^n, with positive minimum. Thus for every H^1 loop

    u ell_h <= ell_g <= v ell_h,       u F_h <= F_g <= v F_h. (2)

No uniform bound on curvature, derivatives of g, or g-injectivity radius follows from (1), and none is used below.

### 1.1 Uniform fixed-degree filling

We explain the uniformity of Source345's shortening construction rather than transfer its conclusion by a multiplicative comparison. Write A_a(g)={ell_g<a}. Let D_h=diam_h(S^n)+1. Use h-minimizing spokes and small h-endpoint connectors exactly as in source shortening-recipes and shortening-block. Their h-lengths are at most D_h and, on a unit interval, their h-Lipschitz constants at most 3D_h. A piece of g-Lipschitz constant at most one has h-Lipschitz constant at most 1/u. Accordingly choose

    L_0 = 2 max{1/u,3D_h},
    K_h = K(h,L_0)

from source shortening-recipes, with h as its fixed metric. Every intermediate recipe has g-length at most v K_h. Set

    D = v D_h,       C = max{v K_h,D+1}.

A spoke followed by a g-unit piece has g-length at most D+1; the whole original suffix is left in place. Therefore the actual block homotopy, not just its endpoints, has g-length at most the original g-length plus C, and its final block has g-length at most D. The constants do not depend on g or the number of pieces. The recipes are continuous in strong H^1; that topology is the same for all metrics on the compact sphere. Their neighborhoods and the number of subdivisions may depend on the input and g.

For each degree j>=0 choose

    B_j=2(D+jC+3),
    a_j=1+max{(j+2)B_j, 2((j+1)C+2)},
    H_j=(j+1)C,       b_j=a_j+2.

The source's g-arclength normalization and colored-star construction apply with these constants. They replace a finite j-cycle at length level a>=a_j by one at level a-1 through level a+H_j. Here the j+1 colors act on different blocks; at each parameter point some block is fully shortened. The source estimate is

    terminal length <= L-L/floor(a/B_j)+D+jC.

If L>=a/2 the saved term is at least B_j/2>D+jC+2; if L<a/2 the rough bound L+(j+1)C<a-1 applies. All time intervals for nonconstant pieces remain positive. Only finitely many iterations are made for each finite cycle. The peak bounds are a-r+H_j at stage r, so they do not add over the stages.

We arrive at a global-null cycle x' in A_(b_j)(g). By (2) it lies in A_(b_j/u)(h). Let d_j(h)>0 be the fixed-degree filling increment of the source for the reference metric h, in the length filtration. It fills x' within h-length b_j/u+d_j(h), and hence within g-length v(b_j/u+d_j(h)). Thus

    d_j^box = 1+max{H_j, v(b_j/u+d_j(h))}                    (3)

is a valid g-length filling increment for every metric in (1), in degree j. If the starting level is already below b_j, the same reference filling applies immediately. All fillings are finite singular chains. This argument also shows explicitly where the lower comparison u is used; it is not discarded in an unsupported one-sided estimate.

### 1.2 Uniform resonance constants

Let d=n-1 and mu_g=lim_m cr_g(Theta^m)/m. The source sphere-powers proposition, and HR v2 section 5 with its proof and section 6 calculations, give mu_g>0 and lambda_g=mu_g/(2d). Equation (2) gives

    u mu_h <= mu_g <= v mu_h.                              (4)

Use the fixed finite set Q of ordinary loop-homology generators in HR Lemma 5.4. For all sufficiently high nonzero homogeneous classes z=Y Theta^m, with Y in Q, equation (19) of the actual HR proof gives

    (m-2)mu_g <= cr_g(z) <= (m+2)mu_g+cr_g(Y),
    |z|=2dm+|Y|,       0<=|Y|<=3n-2.                      (5)

Let C_Q=max_(Y in Q) cr_h(Y). From (4), (5), and cr_g(Y)<=v cr_h(Y),

    |cr_g(z)-|z|lambda_g|
       <= 2v mu_h + v C_Q + (3n-2)v lambda_h.              (6)

This intentionally loose bound is uniform in m and g. Finitely many exceptional low degrees are handled by adding the maximum of v(cr_h(z)+|z|lambda_h) over their fixed finite basis classes. Denote the resulting uniform bound by R_box. Rank-one field duality gives the analogous cohomological estimate; in low degree the constant summand has critical level zero and is included in the finite enlargement. Relative high-degree classes coincide with absolute ones in the degrees used by the cut.

Consequently a uniform dimensionless resonance constant for the source is

    C_H = R_box/(u lambda_h),
    alpha_g=1/lambda_g in [1/(v lambda_h),1/(u lambda_h)].  (7)

The statement is not deduced from a bare multiplicative comparison of an error growing with degree. The bounded error in (5), from the original HR product/BV proof, is essential.

Continuity needs only C^0 comparison. If g' is sufficiently C^0-close to g, for any prescribed epsilon>0 we have (1-epsilon)F_g<=F_g'<=(1+epsilon)F_g. The same inequalities hold for every homological critical level, and hence for mu and lambda after passing to the power limit. Thus lambda is continuous in the topology used in FROZEN.md. Its minimum and maximum on P exist and are strictly positive and finite.

### 1.3 One uniform increment in every fiber and degree

We now carry all parameters through the actual source cut-and-join proof. Choose a single integer J>2n so large that for every j>=J, with

    m=floor((j-2)/(2d)),  q=2md,  p'=q-d,

we have m>=1, p'>n+1, and p'>C_H+2/(u lambda_h). This is a finite, metric-independent choice. Then the source thresholds

    l=(n+q+C_H)/alpha_g+2,
    L=(p'-C_H)/alpha_g-2

satisfy L>0, and

    l-L=(2n-1+2C_H)/alpha_g+4
        <= G_box := (2n-1+2C_H)v lambda_h+4.               (8)

The remainder degree r=j-q lies in [2,2n-1]. Let d_*=max_(0<=s<J)d_s^box and set

    D_0 = G_box+d_*+6.                                    (9)

Take the source cycles S representing Theta^m and cocycles T representing omega^m at these thresholds. For a global-null cycle x of degree j>=J the native cut D_Tx has degree r and length below a-L+1; it remains globally null. Formula (3) gives its filling W. The source's absolute unit identification supplies D_TS-[S^n], which is filled in degree n using (3). The join radius is selected after both finite fillings and their length bounds are known. The source filtered interchange, the two joined fillings, and the unit prism all lie below a+D_0 by (8), (9). This is exactly the chain combination in source ordinary.tex, with uniform constants substituted at the places where they are needed. In degrees j<J use (3).

The source strong H^1 arclength homotopy turns the resulting length filling into an F_g filling without increasing F_g on the original boundary prism. It therefore proves the absolute assertion at every positive open cut, including critical cuts. The chain projection id-i_# ev_# used in the source proves the constants-relative assertion with the same D_0.

This proves part (1), with D_0 from (9) and R=R_box. It also shows why this family uniformity does not assume continuous choices of the power representatives, cocycles, local fillings, or geodesics. They are constructed separately in each fiber. The next step glues homological information, not a chosen fiberwise filling.

## 2. Local-to-total homological descent

For part (2), now fix any D_0>0 and R>=0 satisfying part (1), not necessarily the choices above. We prove a general finite-cover argument with its filtration loss explicit.

### 2.1 A finite-cover filtration and its zero-map property

Choose an open-star cover U_i of a sufficiently fine triangulation of P. Its order is at most p+1. Every nonempty intersection U_I is contractible. For any finite collection of levels, the same cover is used at every level.

The function (t,gamma) |-> F_t(gamma) is continuous: uniform tensor convergence controls the energy difference by the reference H^1 norm, and energy for a fixed smooth metric is continuous in strong H^1. Thus Y_a is open, even for the parameter regularity of the theorem. For an open set Z in P x Lambda, the standard augmented Čech chain complex of the inverse-image cover has columns

    C_(r,q)(Z)= direct sum_(|I|=r+1) C_q(Z over U_I),
    0<=r<=p, q>=0.

The horizontal differential is the sum of omissions of a cover index, and the vertical differential is the singular boundary (signs disappear over F_2). It computes H_*(Z). To see this without an excision assumption for a closed cover, first use singular chains subordinate to the open cover. For each subordinate singular simplex, the augmented horizontal row is the augmented simplex complex of the nonempty set of cover members containing that entire simplex, so it is contractible. Subdivision gives the usual quasi-isomorphism from subordinate chains to all singular chains, and the prism homotopies preserve any subspace under consideration. The same argument, or the quotient of the two resolutions, computes H_*(W,Z), W=P x Lambda, using local pairs (U_I x Lambda,Z over U_I).

Filtering the total complex by cover degree r gives a spectral sequence

    E^1_(r,q)= direct sum_(|I|=r+1) H_q(Z over U_I)

and the analogous sequence for pairs. It converges in every degree because 0<=r<=p. On H_N its filtration has at most p+1 nonzero steps. A map of such resolutions that is zero on E^1 in all positions r+q=N is zero on E^infinity in these positions, so its map on H_N lowers that filtration by at least one. A composite of p+1 such maps is zero on H_N. This last assertion uses the same cover and hence the same filtration for all intermediate levels. No collapse of the spectral sequence is asserted.

### 2.2 The local sandwich

Fix epsilon>0 and put tau=D_0+2epsilon. On any prescribed finite bounded interval of cut levels, uniform C^0 continuity of the metrics allows the cover to be chosen so fine that, for every intersection U=U_I and one t_U in U, the following inclusions hold at every level s in that interval:

    Y_s over U
       subset U x X_(s+epsilon)(g_(t_U))
       subset U x X_(s+epsilon+D_0)(g_(t_U))
       subset Y_(s+tau) over U.                           (10)

For completeness, choose a finite A larger than all levels appearing, including the reference levels in (10). Make the ratios between F_t and F_(t_U) lie between 1-delta and 1+delta, where delta>0 is so small that delta A/(1-delta)<epsilon and delta A<epsilon. This implies both outer inclusions. Such a cover exists independently of individual loops. Its fineness can depend on s and the finite range being considered; its order is still p+1. An intersection is contained in each of its stars, so its metric oscillation is also small.

Because U is contractible, the middle two terms of (10) identify in homology with the fiber sublevels, naturally for inclusions. The same factorization is valid for the local pairs with ambient space U x Lambda.

Two consequences will be used:

LOW. If every nonzero global degree-q class for g_(t_U) has critical level greater than s+epsilon, then H_q(X_(s+epsilon))->H_q(Lambda) is zero. The fiber death property makes the middle absolute map in (10) zero on H_q. Thus H_q(Y_s over U)->H_q(Y_(s+tau) over U) is zero.

HIGH. If every global degree-q class is represented below s+epsilon, then also below s+epsilon+D_0. The pair sequence at the target injects H_q(Lambda,X_(s+epsilon+D_0)) into H_(q-1)(X_(s+epsilon+D_0)), since the map to H_q(Lambda) is surjective. The boundary of a class in H_q(Lambda,X_(s+epsilon)) is a global-null class in degree q-1, killed by the increment D_0. Naturality and the target injection therefore make the middle pair map zero on H_q. For q=0 the same conclusion follows from the reduced endpoint of the pair exact sequence (or from the fact that both spaces meet the connected Lambda). Consequently the actual local pair map from level s to s+tau is zero in degree q.

The reference points may differ between intersections. No coherence of these reference choices is needed: they prove that the actual inclusion maps on the E^1 summands are zero; those actual maps already commute with the Čech differentials.

## 3. Proof of the quantitative bound

Fix k>=0 and a>0. Put omega=lambda_+-lambda_-. Choose

    epsilon = D_0/(4p+8),       tau=D_0+2epsilon.

First suppose

    a+p tau+epsilon < (k-p)lambda_- -R.                   (11)

This inequality implies k-p>0. In each of the p+1 successive maps starting at s=a+r tau, 0<=r<=p, every degree q=k-r' with 0<=r'<=p is at least k-p. Its nonzero global classes have critical levels at least

    q lambda(t_U)-R >= (k-p)lambda_- -R > s+epsilon.

The LOW conclusion applies to every E^1 position on total degree k. Section 2.1, with one common sufficiently fine cover for all these maps, makes

    H_k(Y_a)->H_k(Y_(a+(p+1)tau))

zero. In particular it kills the global kernel.

If (11) fails, set

    A=max{a,(k+1)lambda_+ +R+epsilon}.

For every nonnegative q<=k+1, each global degree-q class has critical level at most q lambda(t_U)+R <=(k+1)lambda_+ +R < A. Thus the HIGH conclusion applies to the local pair maps for all p+1 levels A+r tau, r=0,...,p, on every E^1 position of total degree k+1. Section 2.1 gives

    H_(k+1)(P x Lambda,Y_A)
       -> H_(k+1)(P x Lambda,Y_(A+(p+1)tau)) = zero map.  (12)

Every class in ker[H_k(Y_a)->H_k(P x Lambda)] is a connecting image from H_(k+1)(P x Lambda,Y_a). Map that relative class first to level A and then through (12). Naturality of the connecting map shows that the original kernel class vanishes in Y_(A+(p+1)tau).

The failure of (11) gives

    a >= (k-p)lambda_- -R-p tau-epsilon.

Consequently

    A+(p+1)tau-a
      <= k omega+lambda_+ +p lambda_- +2R+(2p+1)tau+2epsilon
      =  k omega+lambda_+ +p lambda_- +2R
           +(2p+1)D_0+(4p+4)epsilon
      <  k omega+lambda_+ +p lambda_- +2R+(2p+3)D_0.      (13)

The same final upper bound exceeds (p+1)tau in the low case. We have therefore killed every global kernel, at every a>0, by the increment k omega+C of FROZEN.md. This proves beta_k<=k omega+C. The proof used only open sublevels and strict comparison margins, never regular cuts or an isolated-orbit condition. It neither chooses geodesics nor asserts a barcode decomposition.

For the relative assertion let i:P x M->P x Lambda and e:P x Lambda->P x M be inclusion and evaluation at time zero. The chain map Q=id-i_#e_# kills C_*(P x M) and preserves C_*(Y_a) for all a>0. For a relative cycle z, Qz is an absolute cycle representing the same relative class. If z is globally null relative to P x M, write boundary U=z+c with c in C_*(P x M); then boundary QU=Qz. The absolute result fills Qz in the asserted level, proving the relative result without a further loss of constants.

In particular omega=0 gives one degree-independent bound for the total family. This proves part (2).

## 4. The sharp scaling example

Take the unit round metric h, p=1, and f(t)=b-(b-1)t^2 on [-1,1], where b>1. This is a smooth positive family with 1<=f<=b, endpoints f=1 and unique maximum f(0)=b. Put g_t=f(t)^2h. Then

    F_t=f(t)F_h,   lambda(t)=f(t)pi/(n-1),
    omega=(b-1)pi/(n-1).                                 (14)

For m>=1, the class z_m=Theta^m has degree k_m=n+2m(n-1) and round critical level c_m=2pi m. The round filtration has injective maps to global homology over F_2. These facts can be read in HR section 6, and also follow directly from the paid round attachments: the m-th ordinary crossing has rank-one groups in degrees (2m-1)d, 2md, 2md+1, (2m+1)d+1. The constants contribute degrees 0,n. These degrees match the global basis AU^r, U^r of the sphere algebra exactly once, with Theta=U^2. There is no other crossing in any such degree to replace a killed generator. Since its global group has rank one, the generator survives; all finite-stage maps are injective. The degree k_m generator is at the m-th round level 2pi m.

Fix a>c_m and write X_a^h={F_h<a}. In the total Y_a consider the open cover

    U = (Y_a intersect {t<0}) union ([-1,1] x X_(a/b)^h),
    V = (Y_a intersect {t>0}) union ([-1,1] x X_(a/b)^h).  (15)

These are open in Y_a and cover it, since its central fiber is X_(a/b)^h. Their intersection is exactly [-1,1] x X_(a/b)^h. The set U deformation retracts to the left endpoint X_a^h by moving t monotonically to -1: for t<=0 the factor f decreases, and for t>0 membership in U already requires F_h<a/b, which makes the entire path admissible. This homotopy stays in U. The analogous assertion holds for V and the right endpoint. The intersection retracts to its central fiber. Under these identifications its maps to the endpoint homology groups are the ordinary sublevel inclusions. They are compatible with increasing a.

The Mayer--Vietoris sequence therefore includes

    H_(k_m)(X_(a/b)^h)
      -> H_(k_m)(X_a^h) direct-sum H_(k_m)(X_a^h)
      -> H_(k_m)(Y_a),                                   (16)

where the first arrow is the diagonal inclusion over F_2. Let z_m(a) denote the unique lift of z_m to H_(k_m)(X_a^h), available since a>c_m and unique by round injectivity. If c_m<a<=b c_m, its diagonal pair (z_m(a),z_m(a)) is not in the image of the first arrow: otherwise z_m would be carried by X_(a/b)^h with a/b<=c_m, contrary to its round critical level and the open critical-level convention. More explicitly, a finite singular cycle supported in X_c has compact image, so its maximal F_h value is strictly below c; it would force its critical level to be less than c. This also excludes birth exactly in the open cut X_(c_m). Hence it defines a nonzero class w_m(a) in H_(k_m)(Y_a).

This class is globally null, since its two endpoint images in H_(k_m)([-1,1] x Lambda) are both z_m and add to zero. Naturality of (16) shows that w_m(a) maps to w_m(a') and remains nonzero whenever a<=a'<=b c_m. For a'>b c_m the diagonal z_m(a') comes from X_(a'/b)^h, so it vanishes in Y_a'. Thus the argument identifies a whole persistent family of global-null homology classes, with its strict-cut endpoints accounted for. No inference from iterated geodesic images is involved.

If D<(b-1)c_m, choose a>c_m sufficiently close to c_m that a+D<=b c_m. Then w_m(a) survives the increment D. Thus

    beta_(k_m) >= (b-1)c_m.

The conclusion follows by excluding every strictly smaller D in the defining infimum. Since k_m>n+1 and [-1,1] x M has homology only in degrees 0,n, the absolute-to-relative maps in degree k_m are isomorphisms at every level and globally. The same lower bound holds for beta_(k_m)^rel.

Dividing by k_m and letting m tend to infinity yields the lower limit omega along this subsequence. Part (2) gives the opposite limsup bound in every degree. It follows separately for beta and beta^rel that limsup_(k->infinity) beta_k/k=omega. This proves part (3), including the coefficient-one sharpness claim.

## 5. Compatibility and existence of genuine parameter freedom

The constant-frequency regime is nonempty and does not force all metrics to be homothetic. Here is an example with precisely the parameter regularity frozen in the theorem. Start from h round and a nonconstant spherical harmonic phi of degree two. For sufficiently small t>=0 the metrics h_t=(1+t phi)h are positive. Their first scalar-curvature variation is

    d/dt Scal(h_t)|_(t=0) = (n-1)(n+2)phi,

using Delta_h phi=-2(n+1)phi. For all sufficiently small nonzero t, their scalar curvature is nonconstant: evaluate its difference at two points where phi differs and use the nonzero first derivative. Thus they are not homothetic to a round metric. Let lambda(h_t) be the continuous positive scale from section 1 and put

    g_t=(lambda(h_0)/lambda(h_t))^2 h_t.

Since lambda(s^2g)=s lambda(g), this family has constant lambda, and hence constant global mean frequency. It is C^0-continuous in t, every fiber is smooth, and the nonconstant curvature persists under its spatially constant rescaling. This uses exactly the allowed regularity; no smoothness of lambda as a function of t is asserted. It confirms that the normalized regime has actual nonhomothetic examples.

The proof concerns total-space homology for this explicit parameter space. It claims no continuous selection of closed geodesics, no persistence of distinct prime images in a limit, no uniform finite-energy prime count, no positive entropy and no extension to Finsler, magnetic, Reeb, orbifold or boundary settings. The length scale in (14) belongs to critical homology classes, whose representatives can be iterated loops; it is never advertised as a prime-image length spectrum.
