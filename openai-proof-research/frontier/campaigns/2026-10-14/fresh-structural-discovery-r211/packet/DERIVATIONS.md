# Source335 integrated derivations — exploratory, no frozen nominee

This is a research record, not a manuscript or a contribution verdict. The two pinned Source335 papers and all their compatible proof operations are stipulated true. Write p=n/2 and E_g(U)=integral_U (Scal_g^-)^p dV_g. The dimension-only positive constant a_n below is exactly an available constant in the stipulated closed-manifold theorem; no optimization is asserted. All simplicial norms in this record have real coefficients.

## 1. A complete corner-smoothing construction

Let W_1,...,W_k be compact oriented smooth n-manifolds, n>=3, with smooth metrics up to their boundaries. Glue some boundary components in pairs by orientation-reversing isometries of their induced metrics. Suppose every seam satisfies H_1+H_2>=0, where each H is the trace of the second fundamental form with the outward normal. Unpaired boundary components, if any, will be treated separately below. No bound on the individual principal curvatures is assumed. For a fixed finite collection of pieces all collar constants below are finite and may depend on those metrics.

Use signed Gaussian coordinates at a seam, with g=dt^2+h(t), h continuous, smooth separately on t<=0 and t>=0. Define J=h'(0+)-h'(0-), and H_- and H_+ using the SAME normal +partial_t. Thus H_-−H_+=H_1+H_2 and tr_{h(0)}J=−2(H_1+H_2). The scalar identity is

 R(g)=R(h)−tr_h h''+(3/4)|h'|_h^2−(1/4)(tr_h h')^2.                 (1.1)

Indeed A=h'/2, H=tr_h h'/2, H'=tr_h h''/2−|h'|_h^2/2, and the Gauss formula R(g)=R(h)−|A|^2−H^2−2H' gives (1.1). This fixes both sign and normalization independently of any OCR of a primary formula.

Choose a nonnegative smooth mollifier phi of integral one, supported in [-1,1], and a smooth sigma supported in (-1/2,1/2), equal to 1/100 on [-1/4,1/4], with 0<=sigma<=1/100. Set s_delta(t)=delta^2 sigma(t/delta) and

 h_delta(t)=integral h(t−s_delta(t)y)phi(y)dy.

This is Miao's actual variable-radius smoothing (2002 v1 and v3, section 3), used here locally on a compact collar. It equals h for |t|>=delta/2 and differs from h by O(delta^2), including tangential derivatives through order two. In the transition region delta/4<=|t|<=delta/2 the convolution never crosses the seam when delta is small. Differentiating there gives bounded first derivatives because s_delta'=O(delta), and bounded second derivatives because s_delta''=O(1), h' and h'' are bounded on the respective original side. Tangential curvature remains bounded. In the central region the radius epsilon=delta^2/100 is constant, and distributional differentiation gives

 h_delta''=(h''_regular)*phi_epsilon+J phi_epsilon(t).

On the support of the last term, h_delta(t)−h(0)=O(epsilon); hence

 −tr_{h_delta}J phi_epsilon(t)
 =2(H_1+H_2)phi_epsilon(t)+O(epsilon)phi_epsilon(t).

The last summand is uniformly bounded. Every other term in (1.1) is bounded independently of delta. Therefore R(g_delta)>=−C throughout the shrinking collar if H_1+H_2>=0. Although positive scalar curvature may diverge at the seam, its negative part does not. The collar volume is O(delta). For smooth original metrics the construction is smooth: near the seam constant-radius convolution smooths the normal variable; away from the seam the integrand is smooth, including where sigma vanishes. The tangential variables retain smoothness by differentiation under the integral. Thus no downstream regularity upgrade is being assumed.

Summing finitely many disjoint collars proves

 lim_{delta->0} E_{g_delta}(glued manifold)=sum_j E_{g_j}(W_j).       (1.2)

The contribution removed from the original collars tends to zero by their bounded curvature and vanishing volume; the added negative-curvature contribution is at most C^p O(delta). This is convergence of the critical integral itself, not a distributional scalar-curvature inference. This derivation is a compatible classical smoothing operation, fully credited to Miao, not a new operation.

For a double DW, the signed collar is h(|t|), the inward derivative is h'(0)=−2II_out, and H_1+H_2=2H_out. Thus H_out>=0 suffices, including H_out=0 with nonzero trace-free second fundamental form. Product collars are unnecessary.

## 2. Exact topology and the boundary consequence already paid

Assume each boundary component of each W_j has amenable fundamental group. If the paired gluing map identifies the two kernels of the inclusion homomorphisms from the seam fundamental group to the respective piece groups, the gluing is compatible. Theorem 3 and the complete proof in sections 2–6 of Bucher–Burger–Frigerio–Iozzi–Pagliantini–Pozzetti (arXiv:1305.2612v1) give

 ||W,partial W||=sum_j ||W_j,partial W_j||.                         (2.1)

The mechanism is important. Quotient the seam group by the common kernel; its amenable image embeds in each vertex group. Van Kampen gives the graph of groups. The amenable-boundary relative-to-absolute bounded-cohomology map is isometric even when the original boundary inclusions are not injective. The Bass–Serre barycenter cochain extension is norm nonincreasing, extends all vertex cocycles simultaneously, and yields the >= direction by pairing. The <= direction follows by restricting a norm-one dual cocycle, or by gluing almost minimizing relative cycles with small boundary. Thus noninjectivity is not an unpaid gap here. In a double the two kernels agree automatically.

If all boundary components are paired and the result is closed, combine (1.2), the stipulated Source335 inequality on each smoothed closed component, and (2.1):

 sum_j E_{g_j}(W_j)>=a_n sum_j ||W_j,partial W_j||.                 (2.2)

If the glued manifold still has boundary, require H>=0 on its remaining boundary and double it. Smoothing the doubled finite piece system and using compatibility on all seams gives the same (2.2). For a single W the particularly useful consequence is

 E_g(W)>=a_n ||W,partial W||                                      (2.3)

for smooth g, compact oriented W, n>=3, amenable boundary, and outward H>=0. No pi_1-injectivity condition is needed. Smooth doubles have norm 2||W,partial W||, while their energies tend to 2E_g(W), so the constant is exactly the source a_n. These are completed source/classical compositions; no substantial-contribution claim is made.

Without compatible gluing, the actual primary theorem only gives ||W,partial W||<=sum_j||W_j,partial W_j||; this is the wrong direction for inferring the sum on the right of (2.2) from the closed source bound. Without amenability, even pi_1-injective doubles need not have twice the relative norm. These are topology limitations of this particular construction, not evidence of priority elsewhere.

## 3. Critical concentration when the mean-curvature sign is wrong

The same smoothing makes the boundary error visible. If H_1+H_2<0 on a set of positive boundary measure, its central scalar term is negative of size epsilon^{-1}|H_1+H_2|. In the construction above, for a fixed such seam and p>1,

 epsilon^{p−1} integral_{central collar} (R(g_delta)^-)^p dV
 -> 2^p (integral phi(s)^p ds) integral_seam ((H_1+H_2)^-)^p dA.    (3.1)

To see this, put t=epsilon s, use uniform h_delta(epsilon s)->h(0), multiply R by epsilon in (1.1), and use bounded convergence on the fixed compact s support. The bounded regular remainder vanishes after multiplication by epsilon; positive parts are continuous. Outside the central interval the scalar is uniformly bounded. Thus the cost grows as epsilon^{1−p}=delta^{2−n} when the integral on the right is positive. A formally vanishing collar has nonvanishing and generally divergent critical scalar cost. This calculation disproves only the zero-cost claim for this smoothing; it does not rule out every alternative collar design.

## 4. A weighted and Robin version already paid by a conformal change

Let phi be a smooth real function on a compact smooth W, define
 S_phi=R_g−2Delta_g phi−|d phi|_g^2,
with Delta=div grad, and suppose the outward boundary condition H_g+partial_nu phi>=0 holds. Put u=phi/(n−1), gbar=e^{2u}g. Direct conformal formulas give

 R_gbar=e^{-2u}(S_phi+|d phi|^2/(n−1)),
 H_gbar=e^{-u}(H_g+partial_nu phi).

Since 2p=n, the volume factor cancels the curvature factor exactly. Thus

 E_gbar(W)<=integral_W (S_phi^-)^p dV_g,

and (2.3) proves the same lower bound a_n||W,partial W|| for the last integral when the boundary is amenable. For a closed W there is no boundary condition. The measure is dV_g, NOT e^{phi}dV_g; this observation does not assert a weighted-measure inequality. This formulation is a conformal re-expression of a paid construction. It does not require minimizing a Yamabe functional or assuming an infimum is attained.

## 5. A complete controlled-end construction, including an averaged cutoff

Let M=int(V), where V is a compact connected oriented smooth n-manifold, n>=3, and every component of partial V has amenable fundamental group. Suppose a compact core has finitely many smooth product ends Sigma_i x [0,infinity), each carrying

 g=dt^2+h_i(t).

Here Sigma_i is closed, h_i(t) is a smooth family of metrics, R_i(t) denotes its intrinsic scalar curvature, and H_i(t)=tr_{h_i(t)}h_i'(t)/2 is the trace mean curvature toward increasing t. This metric is complete: escaping a compact subset through any end requires t->infinity and has infinite length. There is no bound on sectional curvature, Ricci curvature, the trace-free part of h_i', or the end injectivity radius.

Fix any length L>0. Assume E_g(M)<infinity and, on the ends,

 integral [(R_i(t)^-)^p+(|H_i(t)|/L)^p] dA_{h_i(t)}dt < infinity.   (5.1)

Finiteness of the second term is independent of which fixed L is used. No finite-volume assumption is needed for this construction. If E_g(M)=infinity the desired inequality below is automatic, so the finite case is the operative one.

Choose a fixed smooth nonincreasing function q:[0,1]->[0,1], equal to 1 near 0 and equal to 0 near 1. Put eta(s)=L integral_0^{s/L}q(v)dv for 0<=s<=L. Then eta(s)=s near 0, eta is constant cL near L with 0<c<1, 0<=eta'<=1, and |eta''|<=C/L. At a chosen end height T, replace the infinite part t>=T by the finite collar

 g_T^cap=ds^2+h_i(T+eta(s)), 0<=s<=L.

It agrees to all orders with the original metric at s=0 and is a product near s=L. This attaches no topological filling: it only changes the metric on a truncated collar of the same compact core. Hence the resulting compact manifold V_T is diffeomorphic to V and its boundary is totally geodesic.

Apply (1.1) to the reparametrized family. All trace-free quadratic terms scale by eta'^2, giving the EXACT identity

 R_cap(s)=eta'(s)^2 R_g(T+eta(s))
          +(1−eta'(s)^2) R_i(T+eta(s))
          −2eta''(s)H_i(T+eta(s)).                               (5.2)

Consequently, with C_p depending only on n and the fixed profile q,

 E(cap_T)<=C_p integral_0^L F(T+eta(s))ds,                         (5.3)

where
 F(t)=integral_{Sigma_i} [(R_g(t)^-)^p+(R_i(t)^-)^p
                          +( |H_i(t)|/L )^p] dA_{h_i(t)}.

The inequality uses (a+b+c)^p<=3^{p−1}(a^p+b^p+c^p) and the uniform eta'' bound. It does not replace a scalar-curvature hypothesis by a Ricci hypothesis.

Averaging avoids any unjustified control of jets on a selected slice. For every R,

 integral_R^{R+L} E(cap_T)dT
 <= C_p integral_0^L integral_R^{R+L} F(T+eta(s))dT ds
 <= C_p L integral_R^{R+2L}F(t)dt.

Thus some T_R in [R,R+L] satisfies

 E(cap_{T_R})<=C_p integral_R^{R+2L} F(t)dt ->0.                  (5.4)

This handles the plateau eta'=0 as well: the averaging is over T, not division by eta', so no singular inverse-Jacobian estimate is hidden. By (5.1) and finite E, F is integrable. Choose such a T separately for each of the finitely many ends. The resulting metrics g_j on compact V_j have product boundary and

 limsup E_{g_j}(V_j)<=E_g(M).

Their cores exhaust M, and the removed original tail energies tend to zero. Apply (2.3) to each V_j. Their relative fundamental classes identify with [V,partial V], giving

 E_g(M)>=a_n ||V,partial V||=a_n ||M||_lf.                        (5.5)

The final norm is the ordinary locally finite REAL simplicial norm, not integral-foliated or Lipschitz simplicial volume. The equality is the actual amenable-end theorem of Kim–Kuessner, arXiv:1205.1375v3, Corollary 3.5. Its proof in section 3 uses the amenable relative bounded-cohomology isometry and the existence of a finite-norm locally finite fundamental cycle. The latter can also be seen concretely as follows.

Use BBFIPP's equivalence theorem to choose a finite relative fundamental cycle c of V with ||c||<=||V,partial V||+epsilon and ||partial c||<=epsilon. In each boundary component choose homologous fundamental cycles z_j with ||z_j||<=epsilon 2^{-j} (start with the corresponding component of partial c, whose norm is <=epsilon). Amenability gives vanishing real simplicial volume and the uniform boundary condition: each z_j−z_{j+1} bounds a finite chain b_j with ||b_j||<=U(||z_j||+||z_{j+1}||), where U is fixed for this boundary chain complex. Place the z_j at levels j of the collar; join adjacent levels with the usual prism, of norm at most n||z_j||, and put the b_j at the next level, choosing signs so the boundary of the whole tail is −partial c. This produces a locally finite cycle: each compact set meets only finitely many slabs, and each slab contains only finitely many simplices. Its norm is at most ||c||+C(n,U)epsilon. Local orientation on the initial core and the collar prism shows it is [M]_lf. The opposite inequality follows by restricting any locally finite fundamental cycle to the finitely many simplices meeting a compact core and passing to H_n(M,M−core). Their norm is no larger than the original chain norm. Let epsilon decrease to zero. This explains both finiteness and exact norm preservation without confusing finite-norm with uniformly Lipschitz chains. The uniform boundary condition is a paid classical input, explicitly used in BBFIPP section 6; it is not newly proved here.

The strongest integrated operation in (5.5) is therefore: scalar reparametrization identity + averaging + product-boundary doubling + exact amenable norm gluing. This is a completed cutoff/doubling consequence, not a frozen new theorem or an assertion of substantial contribution.

### Explicit cusp test and scale dependence

For an end dt^2+e^{-2kt}h_0 with k>0 and h_0 flat on a closed (n−1)-manifold, put m=n−1. Directly,

 H=−mk, R_i=0, R_g=−m(m+1)k^2,
 dV=e^{-mkt}dA_{h_0}dt.

Both the original critical integral tail and (5.1) are finite. With a cutoff length L, (5.2) yields

 |R_cap^-|<=m(m+1)k^2+2Cm k/L,
 E(cap_T)<=L Vol(h_0)e^{-mkT}[m(m+1)k^2+2Cm k/L]^p.              (5.6)

The exponential factor dominates for fixed k,L. In particular the boundary error really tends to zero; it is not dismissed solely because the boundary area shrinks. Constants are explicit in k and L. For a varying family one must bound the displayed whole expression, or use uniform tails in (5.4); a constant for a fixed cusp cannot silently be reused across changing metrics.

### What this does not prove

Finite E_g(M), even with finite volume, does not imply (5.1). Identity R_g=R_i−|A|^2−H^2−2H' involves a derivative and allows cancellation; it supplies no standalone control of negative R_i or |H|^p. The source's measured noncompact degree theorem is already valid on controlled incomplete bands, but applying it to an arbitrary end still requires a detector with the relevant finite chart, measure, boundary-buffer and derivative controls, and a compatible entropy construction. Those source operations do not establish these end hypotheses automatically. To remove (5.1) by this route one would have to construct collars with vanishing critical negative-scalar cost while preserving the relative or locally finite class from E alone. No such construction is supplied here. This is an unresolved obligation, not a claimed new result or favorable priority evidence.

## 6. Quantitative-coercivity and rigidity routes tested to their paid endpoint

On a closed n-manifold, Holder yields E_g>= (integral R_g^-)^p Vol(g)^{1−p}; the converse comparison is not available without an additional bound. The source directly gives ||R_g^-||_{L^p}>=a_n^{1/p}||M||^{1/p}, and if R_g>=−K then K^p Vol(g)>=a_n||M||. The latter implication makes no Ricci, sectional or injectivity-radius assertion. Passing to finite covers or a degree-d map only uses multiplicativity or degree monotonicity of the REAL norm and preserves the same source operation.

The companion's rational inessentiality conclusion is stronger than vanishing real simplicial volume, but rational essentiality alone gives no dimension-only positive lower bound for inf_g E_g: a torus is rationally essential and has a flat metric with E=0. The companion obstructs strictly positive scalar curvature there, not scalar-flat metrics. Hence a replacement of ||M|| by a binary rational-essentiality indicator is false.

Even volume normalization cannot turn E->0 into geometric compactness. Let T^n have rectangular flat side lengths L, L^{-1},1,...,1. The volume is one, E=0, diameter tends to infinity and injectivity radius tends to zero. All are flat, consistent with the companion, but the normalized metrics have no uniform compactness of the claimed type.

Even on a fixed flat torus, small critical scalar energy cannot give a curvature supremum estimate. Fix a compactly supported smooth bump psi in a coordinate ball, with Delta psi(0) nonzero, and let u_r(x)=r psi(x/r). Put g_r=e^{2u_r}g_0, extended by g_0 outside the radius-r ball. The conformal formula gives |R_{g_r}|<=C/r on the support and zero elsewhere, so E_{g_r}<=C r^{n-p}=C r^{n/2}->0, while |R_{g_r}(0)| grows as c/r. Rescale by a constant to restore volume one; that factor tends to one and E is invariant under it. These metrics converge uniformly to g_0 but have unbounded curvature, hence cannot converge in C^2. This construction is elementary and is only a countercheck on a proposed inference, not a research nominee.

Under an explicitly assumed compact normalized family in the smooth topology, consisting of positive-definite smooth metrics on a fixed closed aspherical manifold, a qualitative stability statement does follow routinely: any sequence with E->0 has a smoothly convergent subsequence; continuity of scalar curvature and the volume form makes the smooth limit nonnegative-scalar; the stipulated companion makes that limit flat. Thus distance to the flat locus in, for example, the C^2 topology tends to zero. The smooth compactness assumption is explicit; a merely C^2 limit is not silently submitted to a theorem stated for smooth metrics. This is compactness plus qualitative rigidity, with no effective modulus and no compactness theorem derived from scalar energy. A numerical rate would require an additional analytic estimate after these paid steps. None is established here.

## 7. Carrying the stronger rational obstruction through the double

The norm consequence is weaker than what a compatible use of the companion gives. Here is that use, including its analytic and group-homological steps. This remains an exploratory completed composition, not a frozen substantial nominee.

Let W be compact connected oriented smooth of dimension n>=3. Let g be smooth to the boundary, with R_g>=0 and outward H>=0. For this paragraph assume either R_g is positive at some point or H is positive at some point. Boundary fundamental groups need NOT be amenable. Then the following construction makes a smooth positive-scalar-curvature metric on DW.

### Spectral repair of the corner smoothing

Use the smoothing of section 1 and fix a smooth background metric g_* on DW. The metrics g_delta are uniformly comparable to g_*, and converge uniformly to the reflected continuous metric. Their Sobolev constants for H^1->L^{2n/(n−2)} are consequently bounded uniformly. Away from the delta-collar, R_delta>=0; inside it R_delta>=−C, and its negative part has L^{n/2} norm tending to zero. Put a=4(n−1)/(n−2). For every smooth function v, Holder and the uniform Sobolev inequality give

 integral R_delta^- v^2 dV_delta
 <= ||R_delta^-||_{L^{n/2}} ||v||_{L^{2n/(n−2)}}^2
 <= o(1)(||dv||_{L^2(g_*)}^2+||v||_{L^2(g_*)}^2).                (7.1)

If R_g>0 somewhere, choose a fixed open ball U away from the seam where R_g>=kappa>0. On the connected compact double, the fixed quadratic form

 ||dv||_2^2+integral_U v^2

controls ||v||_{H^1}^2. Proof: otherwise a normalized L^2 sequence with gradient tending to zero would converge in L^2 to a nonzero constant by Poincare, while its norm on U tends to zero, a contradiction. Uniform comparability and (7.1) then show the conformal-Laplacian form

 Q_delta(v)=integral (a|dv|_{g_delta}^2+R_delta v^2)dV_delta

is strictly positive for all nonzero v and small delta.

If instead H>0 somewhere, choose an open boundary patch P where H>=h>0. On its central smoothing layer, the calculation of section 1 gives R_delta>=4h phi_epsilon−C, epsilon=delta^2/100. The smooth mollifier can be taken strictly positive on a smaller interval, so this gives a positive layer measure with mass bounded below independently of delta. The elementary uniform trace estimate is

 epsilon^{-1} integral_{P x [-epsilon,epsilon]} |w|^2 dV_*
 <= C ||w||_{H^1(DW,g_*)}^2.                                    (7.2)

For completeness, apply the one-dimensional inequality |w(x,t)|^2<=2|w(x,0)|^2+2|t| integral_{-|t|}^{|t|}|partial_t w(x,s)|^2ds, integrate in t/epsilon and x, and then use the usual trace inequality on the fixed compact collar. Its constants are independent of epsilon. If the sum of the gradient energy and the positive layer term failed to control ||v||_2^2 uniformly, take ||v_j||_2=1 with those two terms tending to zero. Poincare makes v_j−c_j tend to zero in H^1, with |c_j| bounded away from zero along a subsequence. Estimate (7.2) makes the weighted layer norm of v_j−c_j tend to zero, whereas the layer norm of c_j stays bounded below. This is a contradiction. The positive form thus has a uniform H^1 coercivity constant. Apply the same estimate as (7.1) to the remainder C times the indicator of the shrinking collar; its L^{n/2} norm tends to zero, so that remainder is absorbed. This proves strict positivity of Q_delta also in this case.

For each fixed small delta, the first eigenfunction u_delta of the smooth self-adjoint elliptic operator −a Delta_{g_delta}+R_delta is smooth and strictly positive on the connected closed double, by minimization of its Rayleigh quotient and the strong maximum principle. Its eigenvalue lambda_delta is positive by the preceding coercivity. The conformal metric u_delta^{4/(n−2)}g_delta therefore has scalar curvature

 lambda_delta u_delta^{-4/(n−2)}>0.

This uses an attained first linear eigenvalue on a compact manifold, not an assumed minimizer of an arbitrary nonlinear Yamabe infimum. All constants used to choose delta may depend on the fixed W,g. There is no uniform spectral gap assertion for a changing family.

### Relative class and the graph of groups

Put A=pi_1(W) and, for each connected boundary component Sigma_i, put C_i=im(pi_1(Sigma_i)->A), with fixed compatible base paths. Use classifying spaces BA and BC_i, and interpret H_n(BA,{BC_i};Q) as the homology of the mapping cone of the disjoint union of the inclusions BC_i->BA. This convention matters: the edge groups are the IMAGES C_i, not silently the original pi_1(Sigma_i). The classifying map of W and its boundary factorizations induce a relative class

 alpha_W in H_n(BA,{BC_i};Q).

To identify the double, take a graph of spaces X with two copies BA_+,BA_- and an edge cylinder BC_i x [0,1] for each boundary component. Van Kampen gives the double group: the two boundary homomorphisms have the same kernel, so quotienting the boundary group by that kernel gives precisely the injective edge maps C_i->A. The universal cover of X is a tree of contractible vertex and edge spaces, hence X is a K(pi_1(DW),1). Classifying maps on the halves can be chosen compatibly on collars, giving a classifying map f:DW->X.

Let K consist of BA_- and the half of every edge cylinder adjacent to it. The quotient pair (X,K) has the homology of the mapping cone (BA_+,{BC_i}). Under

 H_n(X;Q)->H_n(X,K;Q)=H_n(BA,{BC_i};Q),

the image of f_*[DW] is exactly alpha_W: the second half is killed, and the first half becomes the relative fundamental cycle with its boundary factorizations. This is a chain-level consequence of the collar decomposition, so cancellation between the two absolute vertex contributions does not invalidate it.

The stipulated companion applies to the smooth PSC metric constructed above and gives f_*[DW]=0 in H_n(X;Q). Therefore alpha_W=0. In particular, nonzero alpha_W obstructs the simultaneous conditions R>=0, H>=0, with R or H somewhere strictly positive. If boundary is empty, this reduces to the companion's familiar closed case. For a relative degree map inducing a homomorphism of these group pairs, naturality transfers this vanishing; one must specify that pair homomorphism before using a target obstruction.

This completes the strongest direct doubling route for the rational class in question, without an amenability or boundary-injectivity assumption. It is a consequence of classical corner smoothing, a compact spectral/conformal repair, graph-of-groups topology, and the stipulated companion. It is not evidence for an additional substantial operation. The fully degenerate case R=0 and H=0 is intentionally not given a new rigidity conclusion here; integral-energy convergence alone does not supply a smooth nonnegative-scalar metric on the double, and the nonsmooth seam may still have trace-free second fundamental form.
