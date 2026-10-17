# O234 — All-temperature pressure with bounded spectral outliers

Author: Myeongjin Kang (no affiliation). Original exposition CC BY 4.0; original code MIT. This is an author proof of the unchanged target in original-scope.md, not an independent verdict. Upstream theorems at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. The pre-freeze feasibility and comparison records preserve chronology.

## 1. Statement and exact functional

Let Lambda_N=diag(lambda_{1,N},...,lambda_{N,N}) be deterministic real diagonal matrices, uniformly bounded in operator norm. Suppose their empirical measures converge weakly to a probability measure mu, and their largest eigenvalues converge to theta. Write a=min supp(mu), b=max supp(mu); necessarily theta>=b. No convergence of the smallest eigenvalue is assumed. All eigenvalues, including all outliers, remain uniformly bounded. Let U_N be Haar on O(N), with arbitrary dependence across N. For beta>=0 put

(1) P_N(beta)=N^(-1) log[2^(-N) sum_{sigma in {-1,1}^N} exp{(beta/2) sigma^T U_N^T Lambda_N U_N sigma}].

**Theorem O234.** In expectation and almost surely, P_N(beta) converges locally uniformly on [0,infinity) to F(beta_*mu,beta theta), defined below. Thus finite and arbitrary sublinear families of positive outliers are included; only their largest limit survives in this pressure. Bounded negative outliers have no limiting effect. Atomic and point-mass mu are included. Counting measure instead of uniform probability adds log2.

For a compact probability law rho and t>=max supp(rho), define H_rho(z)=integral (z-lambda)^(-1)rho(dlambda), z>t. For x>0 let b_(rho,t)(x) be the unique z>t with H_rho(z)=x, if it exists, and otherwise t. Put

(2) R_(rho,t)(x)=b_(rho,t)(x)-1/x,  R_(rho,t)(0)=integral lambda rho(dlambda).

This is an inverse branch capped at an actual extreme, not analytic continuation. Let P be the nondecreasing measurable functions p:(0,1)->[0,1], modulo null sets, and set

(3) D_p(r)=1-r-integral_0^1 (p(s)-r)_+ ds, 0<=r<=1.

The entropy functional S is exactly the pinned source's. For completeness, let h be any nonnegative nondecreasing finite step function on (0,1), with successive interval lengths w_i>0 summing to one and heights h_i, i=0,...,k-1. Write zeta_i=sum_{l<i}w_l and h_{-1}=0. For a,v>=0 and standard normal g define T_(a,v)f(z)=a^(-1)log E exp[a f(z+sqrt(v)g)] if a>0, and E f(z+sqrt(v)g) if a=0. Starting F_{k-1}(z)=log cosh z, recursively put F_{i-1}=T_(zeta_i,h_i-h_{i-1})F_i for i=k-1,...,0, and ell(h)=F_{-1}(0)-h_{k-1}/2. Then

(4) S(p)=sup_h {ell(h)+(1/2)integral_0^1 p(s)h(s)ds},
    F(rho,t)=inf_{p in P}{S(p)+(1/2)integral_0^1 R_(rho,t)(D_p(r))dr}.

All suprema/infima retain their displayed order. The source proves S>=0, S(0)=0 and 0<=D_p<=1. The transform below is bounded, so F is finite. At beta=0, rho=delta_0,t=0,R=0 and F=0.

## 2. Antecedents and the missing comparison

The pinned family234 Theorem thm:main supplies (4) when BOTH extreme eigenvalues converge to the support edges, with t=max supp(rho). Its general-spectra section already proves operator-norm comparison, monotonicity, qualitative capped-transform continuity and a relative multiplicity bound. We use this theorem as given. Its positive-mass count bound does not compare one spike to epsilon N spikes with error tending to zero: the denominator contains the smaller multiplicity. Source source-map/read-limits records identify exact bodies.

Guionnet–Maida's Theorem1.6 already identifies the extreme-eigenvalue cap in spherical integrals, and Bhattacharya–Sen permits outlier limits in a high-temperature Ising theorem. Fan–Wu already permits bounded lower outliers at high temperature; Fan–Misiakiewicz–Wang–Wen v2 allows bounded outliers under its explicit small-norm condition. No claim of novelty attaches to the cap, high-temperature cases or lower-outlier permission alone. The proposed additional operation is Section4: a finite-N comparison of quenched Ising pressures after thickening a single outlier to a small positive spectral fraction, while preserving its correlation with the Haar bulk.

We also use the classical Haar concentration inequality, in the exact pressure form derived in Fan–Wu Section5. If a deterministic symmetric A has norm at most L, then for N>=4,

(5) Pr(|P_N(A,U)-E P_N(A,U)|>s) <= 2 exp[-N s^2/(16 L^2)].

For L=0 the pressure is constant. A larger bound L>=1 may always be used. This does not require high temperature: the derivative estimate in that proof is ||d_U P_N||_F<=||A||_op, using ||sigma||^2=N; sign-flipping an eigenvector identifies the two components of O(N). Gromov concentration on SO(N) gives (5). The high-temperature hypothesis enters their separate moment calculation, not this concentration estimate. No independence of multiple pressures evaluated at the same U is needed below.

We write f_N(d)=E P_N(diag(d),U), with temperature absorbed in d. Elementary comparisons give

(6) |P_N(A,U)-P_N(B,U)|<=||A-B||_op/2,
    A<=B implies P_N(A,U)<=P_N(B,U).

These follow term by term in the positive spin sum and hold for any fixed prior on the cube. Haar invariance makes f_N a symmetric smooth convex function of its N eigenvalue coordinates.

## 3. Removing bounded lower outliers

**Lemma1.** If d^(N) is uniformly bounded, its empirical laws tend weakly to mu, and a=min supp(mu), then

(7) f_N(max(d^(N),a))-f_N(d^(N)) -> 0,

where max is coordinatewise. This statement does not require a top-edge limit.

**Proof.** Smoothness and differentiation of the finite sum give

(8) partial_i f_N(d)=(1/(2N)) E< (U sigma)_i^2 >_d >=0,
    sum_i partial_i f_N(d)=1/2.

Convexity and symmetry imply ordered derivatives: if d_i<=d_j, then partial_i f_N(d)<=partial_j f_N(d). Indeed exchange i,j to obtain d'; convex gradient monotonicity gives
0<=(grad f_N(d)-grad f_N(d')) dot(d-d')
=2(d_i-d_j)(partial_i f_N(d)-partial_j f_N(d)). Equality of coordinates gives equality of derivatives by symmetry, so the ordering holds also at ties.

Fix delta>0. Raise only coordinates below a-delta to a-delta. Their number q_N satisfies q_N/N->0: weak convergence and support(mu) in [a,infinity) give limsup mu_N((−infinity,a-delta])=0 by the closed-set bound. During the straight raising path, each changed coordinate stays no larger than every unchanged coordinate. By (8) and derivative ordering, every changed-coordinate derivative is at most 1/[2(N-q_N)]. If |d_i|<=K and |a|<=K, the change of each coordinate is at most 2K. Thus, for all sufficiently large N with q_N<N,

(9) 0<=f_N(max(d,a-delta))-f_N(d)<=K q_N/(N-q_N).

Raising the remaining coordinates from that clipped vector to max(d,a) changes each by at most delta, so (6) costs at most delta/2. Take N to infinity then delta down to zero. This proves (7). Neither a positive density of bottom eigenvalues nor a non-atomic edge is assumed. QED.

## 4. The finite-N rank-thickening comparison

**Lemma2.** Let A_0 be deterministic symmetric with ||A_0||<=K, and let E be a k-dimensional eigenspace on which A_0=b I (E need only be a subspace of that eigenspace). Let v_0 be any fixed unit vector in E, a>=0, 0<eta<1, a'=a/(1-eta)^2 and L=1+K+a'. Define A_k=A_0+a Pi_E and A_1=A_0+a v_0v_0^T. For N>=4,

(10) 0<=E P_N(A_k,U)-E P_N(A_1,U)
 <= (a'-a)/2 + (k/N) log(1+2/eta)
       +8 L sqrt([k log(1+2/eta)+log2+1]/N).

All expectations concern a single common Haar U. No law for the Gibbs state or independence among net directions is assumed.

**Proof.** Take an eta-net V of the unit sphere of E of cardinality M<=(1+2/eta)^k. A maximal eta-separated set exists by compactness; its disjoint eta/2 balls fit in the ball of radius1+eta/2 in E, proving this cardinality bound. For y=Pi_E x nonzero choose v in V within eta of y/||y||. Since v dot y/||y||=1-||v-y/||y||||^2/2 >=1-eta, we have

(11) ||Pi_E x||^2 <= (1-eta)^(-2) max_{v in V}(v dot x)^2.

For y=0 the same inequality is immediate. Applying (11) with x=U sigma to the quadratic exponent, then exp(max)<=sum exp, yields the actual partition-function bound

(12) Z_N(A_k,U)<=sum_{v in V} Z_N(A_0+a' vv^T,U),
     P_N(A_k,U)<=max_{v in V}P_N(A_0+a' vv^T,U)+(log M)/N.

Every A_0+a' vv^T has the SAME eigenvalues, since A_0 is scalar on E. A rotation within E carries v to v_0 and fixes A_0. Therefore each pressure in (12) has the same mean m'=E P_N(A_0+a'v_0v_0^T,U). Their norm is bounded by L. Applying (5) and a union bound gives
Pr(max_v(P_v-m')>s)<=min(1,2M exp[-N s^2/(16L^2)]).
Integrating this tail, split at s_0=4L sqrt(log(2M)/N). The integral above s_0 is at most 8L^2/(N s_0), by integral_t^infinity exp(-c s^2)ds<=exp(-c t^2)/(2ct). Consequently

(13) E max_v P_v <=m'+8L sqrt((log(2M)+1)/N).

The constants in (13) are deliberately loose. By (6), m'<=E P_N(A_1,U)+(a'-a)/2. Combine (12),(13), and the net cardinality bound. Finally A_k-A_1=a(Pi_E-v_0v_0^T)>=0 proves the left side of (10). QED.

This lemma applies to a deterministic cube prior, but its use here is solely the frozen zero-field theorem. Its scalar-block requirement is essential; arbitrary directions in a nonflat bulk need not produce identical rank-one spectral laws.

## 5. Continuity with an extreme outside the support

**Lemma3.** Suppose rho_j converge weakly to rho, their supports lie in [-K,K], t_j>=max supp(rho_j), |t_j|<=K, and t_j->t. Then t>=max supp(rho) and

(14) sup_{0<=x<=1}|R_(rho_j,t_j)(x)-R_(rho,t)(x)| ->0,
     |F(rho_j,t_j)-F(rho,t)| <= (1/2)||R_(rho_j,t_j)-R_(rho,t)||_infinity ->0.

This adapts the source's actual capped-transform continuity proof; it is not the proposed contribution by itself.

**Proof.** Increase K to a positive number if necessary. For every such pair and x>0,

(15) t<=b_(rho,t)(x)<=t+1/x,  -K<=R_(rho,t)(x)<=K.

The upper b bound follows from H(z)<=1/(z-t). For the R bounds use H(z)>=1/(z+K) and H(z)<=1/(z-K) where applicable; on the capped branch x>=H(t+)>=1/(t+K), with an infinite lower bound interpreted correctly when t=-K. Hence R=t-1/x>=-K on that branch too, and R<=t<=K.

Take x_j->x>0. Boundedness in (15) gives a subsequential limit b_* of b_j(x_j), with b_*>=t. If b_*>t, then b_j>t_j eventually, the defining equations are uncapped, and uniform separation of arguments from supports plus weak convergence gives H_rho(b_*)=x. Thus b_*=b_(rho,t)(x). If b_*=t but b_(rho,t)(x)>t, choose c strictly between these two numbers. Then H_rho(c)>x and, for large j, c>t_j and H_(rho_j)(c)>x_j; monotonicity forces b_j(x_j)>c, contradiction. Therefore b_j(x_j)->b_(rho,t)(x). Applying the same argument with fixed rho,t proves continuity of b on (0,1]. Sequential compactness gives uniform convergence of R on every [epsilon,1].

For x<1/(4K), no capped branch is possible because H_rho(t+)>=1/(2K). Substitute b=x^(-1)+R in the defining equation. Since |R-lambda|<=2K, expansion of (1+x(R-lambda))^(-1), with remainder at most a universal constant times K^2 x^2, gives

(16) R_(rho,t)(x)=integral lambda rho(dlambda)+O(K^2 x),

uniformly for all pairs. Means converge by bounded weak convergence; (16) extends the uniform convergence to zero. Finally 0<=D_p<=1 makes the G terms differ uniformly in p by half the norm in (14); adding the common S and taking infima proves the second assertion. F is finite because S>=0, S(0)=0 and |G|<=K/2. QED.

## 6. Spectral sandwich and order of limits

We prove first convergence of expected pressures at beta=1. By Lemma1 we may replace the original eigenvalues by their maxima with a; this preserves empirical convergence, the top limit theta and a common norm bound. Order these new eigenvalues d_{1,N}>=...>=d_{N,N}. Let

(17) c_{i,N}=min(d_{i,N},b).

The c-array lies in [a,b], converges empirically to mu, and its extremes tend to a,b. The weak convergence and endpoint assertions follow from bounded clipping and positive mu mass in every neighborhood of its support edges. In particular c_{1,N}->b. Write C_N=diag(c_{i,N}).

If theta=b, then max_i|d_{i,N}-c_{i,N}|=(d_{1,N}-b)_+->0. Equation(6) and the stipulated no-outlier source theorem prove the desired expectation limit F(mu,b). Thus assume theta>b. For all sufficiently large N, d_{1,N}>b. Replace d_{1,N} by theta; equation(6) changes pressure by at most |d_{1,N}-theta|/2. For comparisons below it is equally convenient to keep the original d-array and absorb this vanishing error explicitly.

Fix 0<epsilon<1/4 and put k_N=max(1,floor(epsilon N)). Define

(18) B_(N,epsilon)=diag(theta [k_N times],c_{k_N+1,N},...,c_{N,N}),
     S_N=diag(theta,c_{2,N},...,c_{N,N}).

Let Q_mu(u)=inf{x:mu((−infinity,x])>=u}, 0<u<1. The empirical law of B_(N,epsilon) tends to

(19) nu_epsilon=(Q_mu)_*(Lebesgue restricted to (0,1-epsilon))+epsilon delta_theta.

This is a probability measure. To justify (19), the bounded empirical laws of C_N converge in W1 to mu. Their increasing quantile functions converge to Q_mu in L1(0,1): the usual monotone-quantile coupling identity W1=int|Q_N-Q_mu| follows equivalently by the area identity int|F_N-F_mu| for distribution functions; bounded weak convergence makes the latter tend to zero by dominated convergence at the continuity points of F_mu. Restricting this L1 convergence to (0,1-k_N/N), whose endpoint tends to1-epsilon, gives (19) against every Lipschitz test. Such tests determine weak convergence on the common compact interval. No continuity of the quantile at1-epsilon is required.

Since epsilon<1, min supp(nu_epsilon)=a and max supp(nu_epsilon)=theta. Indeed every sufficiently small neighborhood of a retains positive quantile mass, and the atom at theta has positive mass. The actual B eigenvalue extremes tend to a and equal theta eventually (c<=b<theta). Thus the source theorem applies at EACH FIXED epsilon:

(20) lim_N f_N(B_(N,epsilon))=F(nu_epsilon,theta).

As epsilon decreases to zero, nu_epsilon converges weakly to mu (the altered mass is epsilon); its top edge remains theta. Lemma3 gives

(21) F(nu_epsilon,theta)->F(mu,theta).

We next pay the lower comparison, which is the part unavailable from monotonicity alone. Let A_(N,epsilon) have its first k_N eigenvalues equal b and remaining eigenvalues c_i. On E=span(e_1,...,e_k), it is scalar b. With spike strength A=theta-b>=0, the rank-k spike is exactly B_(N,epsilon); its rank-one spike T_(N,epsilon) has eigenvalues theta,b [k_N-1 times],c_{k_N+1},...,c_N. By(6),

(22) |f_N(T_(N,epsilon))-f_N(S_N)| <= (b-c_{k_N,N})/2.

For each delta>0, mu((b-delta,b])>0. Whenever epsilon is smaller than half this mass, weak convergence implies c_{k_N,N}>b-delta for all sufficiently large N. Hence

(23) lim_(epsilon down to0) limsup_N (b-c_{k_N,N})=0.

Set eta=sqrt(epsilon), so eta<1/2. Applying Lemma2 and k_N/N->epsilon shows

(24) limsup_N [f_N(B_(N,epsilon))-f_N(S_N)]
 <= (1/2) limsup_N(b-c_{k_N,N})
    +(A/2)[(1-sqrt(epsilon))^(-2)-1]
    +epsilon log(1+2/sqrt(epsilon))
    +8(1+K+4A)sqrt(epsilon log(1+2/sqrt(epsilon))).

Here K bounds A_(N,epsilon), and constants independent of N,epsilon were enlarged harmlessly. The right side tends to zero by(23). Since B_(N,epsilon)>=S_N, (20),(21),(24) imply

(25) f_N(S_N)->F(mu,theta).

For clarity, for each fixed epsilon the inequalities give liminf f_N(S_N)>=F(nu_epsilon,theta)-error(epsilon) and limsup f_N(S_N)<=F(nu_epsilon,theta). Taking epsilon down to zero gives (25); no interchange of thermodynamic limits is assumed.

Finally compare the original lower-clipped d-array. Its top eigenvalue d_1 tends to theta, and d_i>=c_i. Consequently

(26) f_N(d)>=f_N(S_N)-|d_{1,N}-theta|/2.

For the upper bound put r_(N,epsilon)=(d_{k_N+1,N}-b)_+. For fixed epsilon, r_(N,epsilon)->0: for every delta>0 weak convergence gives o(N) eigenvalues above b+delta, fewer than k_N eventually. Coordinatewise,

(27) diag(d)<=B_(N,epsilon)+[|d_{1,N}-theta|+r_(N,epsilon)] I.

The first k coordinates are bounded by d_1; for the others d_i<=min(d_i,b)+r. Thus(6), including scalar shift by half the scalar, and (20) imply limsup f_N(d)<=F(nu_epsilon,theta). Now let epsilon decrease to zero and use(21),(25),(26). Reinsert the lower-outlier deletion(7). This proves convergence of E P_N(1) for the full original class.

## 7. All temperatures, almost sure mode and local uniformity

For any fixed beta>0, the scaled spectra beta Lambda_N satisfy the same hypotheses with limit beta_*mu, top beta theta and a uniform bound beta K. Section6 therefore gives E P_N(beta)->F(beta_*mu,beta theta). The case beta=0 is identically zero.

On every finite interval [0,B], for all U,N,

(28) |P_N(beta)-P_N(beta')|<=K|beta-beta'|/2.

It follows directly by comparing every spin energy; the expectation has the same bound. Pointwise convergence on all beta gives that the limiting function has the same Lipschitz bound. A finite rational mesh of [0,B], followed by(28), upgrades expectation convergence to uniform convergence there.

For each fixed positive rational beta and t>0, (5) with L=max(1,beta K) gives a summable bound on Pr(|P_N(beta)-E P_N(beta)|>t). Borel–Cantelli for rational t>0 shows almost sure convergence at that beta. Intersect these probability-one events over countably many rational beta; no cross-size independence is needed. On this single event, (28) and finite rational meshes give uniform convergence on every [0,B] with integer B, hence local uniform convergence on [0,infinity). Moreover |P_N(beta)|<=BK/2 on [0,B], so dominated convergence also gives E sup_{beta in [0,B]}|P_N(beta)-F(beta_*mu,beta theta)|->0. This proves every quantifier in Theorem O234. QED.

## 8. Boundaries of the conclusion

The mechanism preserves a positive top outlier, rather than deleting all rank-o(N) perturbations. The top cap is already an antecedent in annealed spherical integrals; the argument here does not identify quenched and annealed pressure. Norm boundedness is used both in lower-outlier deletion and in exponential concentration. No statement is made for diverging negative eigenvalues. The flat-block comparison is justified before invoking rotational symmetry, and the net pressures remain correlated. Limits occur in the order N first, positive spike fraction second. No assertion about overlap uniqueness, differentiability, fluctuation scale or rate follows. Formal support, if later implemented, would be partial and would not replace the human proof or the stipulated source theorem.

## 9. Independent rank-one stress calculation

Take mu=delta_0 and Lambda_N=diag(theta,0,...,0), theta>0. At inverse temperature beta put s=beta theta. The following direct computation does not use the source variational theorem, Lemma2, or the claimed outlier formula. If u is the first Haar row and v_i=sqrt(N)u_i, then for s>0 the Gaussian identity gives

(29) Z_N= sqrt(Ns/(2pi)) integral_R exp{N[-s t^2/2+N^(-1)sum_i log cosh(s t v_i)]}dt.

The identity follows by integrating exp[-Ns t^2/2+s t sum_i v_i sigma_i] and summing the spins with uniform probability. Under the representation v_i=g_i/sqrt(N^(-1)sum_j g_j^2), with independent standard normals, the strong law and |log cosh x-log cosh y|<=|x-y| imply uniform-on-compact-t convergence of the bracket to -s t^2/2+E log cosh(s t g). The compact uniformity follows by a finite mesh and its deterministic Lipschitz bound in t on compact intervals; the empirical first moments are bounded by the empirical second moments, equal to one after normalization. Also N^(-1)sum log cosh(s t v_i)<=s|t|, so for |t|>=4 the bracket is at most -s t^2/4. Integrating this Gaussian bound controls both tails, while the ordinary compact Laplace bounds give

(30) psi(s)=lim P_N= sup_{t in R}{-s t^2/2+E log cosh(s t g)}.

The Gaussian-row representation proves convergence in distribution under any prescribed Haar coupling across N. Since 0<=P_N<=s/2, expectations converge; (5) then proves almost sure convergence for any such coupling. The maximum in(30) may be restricted to [-2,2], since the displayed upper bound s(|t|-t^2/2) is negative outside and the value at t=0 is zero. For s<=1, log cosh x<=x^2/2 gives psi(s)=0. For s>1, the second derivative at zero is s(s-1)>0, so psi(s)>0.

Finally, 0<=|x|-log cosh x<=log2 implies uniformly in t in [-2,2]
psi(s)/s -> max_t{-t^2/2+|t| E|g|}=(E|g|)^2/2=1/pi.
Therefore the low-temperature slope for the frozen normalization is

(31) lim_(beta->infinity) F(delta_0,beta theta)/beta=theta/pi.

There is a second direct check: max_sigma (theta/(2N))(u dot sigma)^2=theta/(2N)(sum_i |u_i|)^2 ->theta/pi. In this case the capped transform is exactly R_(delta_0,s)(x)=(s-1/x)_+ for x>0 and R(0)=0. For s<=1 this transform vanishes on [0,1], so the source functional itself gives F=inf S=0, directly matching(30). Combining the independently computed(30) with the proved theorem yields the identity between its full source functional and psi(s); this is not a separate direct optimization of that infinite-dimensional functional. The stress check does not audit upstream truth or use a source contradiction. It checks the sign, 1/2 factor, probability normalization, beta scaling, necessity of retaining the spike, and low-temperature slope.
