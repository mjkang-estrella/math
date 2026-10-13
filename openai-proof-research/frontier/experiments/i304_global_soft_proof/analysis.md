# I304 — independent complete proof review of S302

2026-10-13. **PROOF verdict: PASS unchanged.** The frozen S302 analysis has SHA256 `1db6cef312fa1e705c150b1bc2c1ea0484d50915278f602f579074e3dbab6cf8`. Its unrestricted quantifiers are retained. **Supporting sharpness verdict: PASS unchanged**, separately from the upper bound. Neither verdict is an acceptance, contribution, priority or count decision.

## 1. Target, premises and independent review boundary

Let X be uniform on {-1,1}^n, n>=1, and T_r be product noise of correlation r. Define

    psi(t)=((1+t)log(1+t)+(1-t)log(1-t))/2,
    I(u)=E psi(u)-psi(Eu),
    d_a(u)=min_(i,s=±1) E|u-s a X_i|^2,
    Delta_r(u)=psi(ra)-I(T_r u).

For every fixed 0<a0<=a1<1 and 0<r0<=r1<1, there is a finite C depending only on these four endpoints such that every finite n, a in [a0,a1], r in [r0,r1] and u:{-1,1}^n->[-1,1] with exactly I(u)=psi(a) satisfy d_a(u)<=C Delta_r(u). Arbitrary bias, original endpoint values, rare spikes, support and complexity are included. There is no condition on r1*a1. Constants are existential.

The OpenAI theorems and operative lower source results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated as requested. Actual main/scalar/canonical/capacity/reserve/thinning/upgrade/flow passages were read at the authenticated ranges; fresh pinned raw retrievals match all eight local files. The source proof truth was not audited. In particular, `main:soft` covers arbitrary soft kernels at their actual information, and `upgrade:production` bounds interior fields by the maximum profile. The canonical optimizer and retained reserve/thinning operations have the exact physical hypotheses used below. The Hellinger companion's actual theorem is Boolean; it is not a soft stability premise.

All needed internal deductions are checked below, rather than stipulated because old prose calls them accepted. I301's finalized review, complete independent analysis, log, authentication and literature were read and their stated scope checked. Its U300, non-strict Gaussian interface and full Gaussian gap implication are exactly the Gaussian obligations of S302. I301 expressly leaves the old cube chain unchecked; Sections 2–6 below pay it independently. I299 was not accessed while live. Only after the user's supplemental finalization message were its complete final review/analysis/log/literature read; its two supplied hashes match. Its restricted-chain findings agree with these independent checks. Its remaining U295 boundary is filled by U300, not by treating its restricted S295 verdict as an unrestricted theorem. No I303 content was read.

Write L=log 2, H=L-psi, V=atanh, F(psi(t))=t V(t), S=F-2I with zero extension below zero, and

    B_m(J)=2J+(1-m^2)S(L-(H(m)-J)/(1-m^2)),
    Phi_m(J)=max{F(J),B_m(J)}.

The stipulated scalar facts include F(0)=0, F'(0)=2, strict convexity on [0,L), smoothness there, and the stated continuity of S at its seam. All subsequent compact scalar ranges stay below L.

## 2. P128, E128 and E131: the budgets and noise direction

For P_t=T_(exp(-t)), let y(t)=I(P_t u), w(t)=psi(a exp(-t)), z=w-y, and R(t)=D(P_tu)-F(y(t)), with D(g)=E[V(g)Ng]. Source production and contraction give R,z>=0 at positive time. Direct differentiation gives

    w'=-F(w), y'=-F(y)-R,
    z'=R-Az, A=(F(w)-F(y))/(w-y),
    2<=A<=K=max_[0,psi(a1)] F'<infinity.

At w=y use F'. For t=-log r, the integrating factor gives exactly

    Delta=integral_0^t exp(-integral_s^t A) R(s) ds,
    integral_0^t R<=exp(K tmax) Delta,
    z(s)<=exp(K tmax) Delta (0<=s<=t), tmax=-log r0.

The last inequality comes from integrating from s to t and dropping future nonnegative production. It controls *earlier* deficits from the terminal deficit, as S302 needs. Initially endpoint-valued u causes no problem: at every positive time strictly positive finite-cube noise weights make a nonconstant field interior. Integrate first from epsilon>0, use finite-cube entropy continuity z(epsilon)->0, and take the nonnegative improper integral limit. No uniform initial differentiability, finite initial D or dimension-uniform interior margin is required.

For an oriented coordinate with b=E[u s X_i]>=0, strong convexity psi''>=1 gives

    E psi(u)-psi(b)>=E|u-b s X_i|^2/2.

The linear term cancels since V(b s X_i)=s X_i V(b). Exact original information and orthogonality therefore give

    E|u-a s X_i|^2
      <=2[psi(a)-psi(b)+psi(Eu)]+(a-b)^2.       (E128)

This bracket is nonnegative also for b>a. If ||T_lambda u-lambda a s X_i||_2^2=q and lambda>=lambda0>0, constant and singleton coefficients give (Eu)^2<=q and |b-a|<=sqrt(q)/lambda0. Once the latter is <=(1-a1)/2, using psi(m)<=L m^2 yields

    E|u-a s X_i|^2
      <=2 V((1+a1)/2) sqrt(q)/lambda0+2Lq+q/lambda0^2. (E131)

The original information pays the unsmoothed residual. This is not inversion of noise. Its square-root loss is used only to enter a local neighborhood; the final estimate remains linear in Delta.

## 3. Q131b: complete soft compression transfer

Sorting a coordinate fiber replaces b+X_i d by b+X_i|d|. It preserves the full multiset of values, hence mean, M=Eu^2 and exact input information. Other singleton coefficients are preserved because their coordinate is constant on each sorted fiber. Previously acquired monotonicity survives because min and max of ordered pairs remain ordered. Sorting each coordinate once thus produces an increasing kernel g.

On noisy outside coordinates write B=T_r b, D=T_r d and Dplus=T_r|d|. Positivity gives |D|<=Dplus. The even function

    f_B(q)=[psi(B+r q)+psi(B-r q)]/2

has f_B'(0)=0 and f_B''>=r^2 on the interval in question. All arguments lie in [-1,1], since its extreme magnitudes correspond to bounded noisy sorted/unsorted kernels. Integration, followed by endpoint continuity if necessary, gives sorting gain >=(r^2/2)E(Dplus^2-D^2). Thus every sorting step has nonnegative information gain.

Choose i maximizing c=ghat(i)>=0. Before sorting i, Ed is the original singleton b_i, E|d|=c, and Ed^2<=M. Subsequent sorts preserve this singleton. Jensen and the nonconstant spectral bound give

    E Dplus^2-E D^2
      >=(1-r^2)(c^2-b_i^2)-r^2(M-c^2).

For total gain Lgain=I(T_r g)-I(T_r u), it follows that

    (1-r^2)(c^2-b_i^2)<=2Lgain/r^2+r^2(M-c^2).

There is no Boolean derivative identity here. Also d_a(g)=M+a^2-2ac=(M-c^2)+(a-c)^2. If d_a(g)<=a^2/4, then c>=a/2 and

    d_a(u)-d_a(g)<=2a(c-|b_i|)<=4(c^2-b_i^2).

Substitution gives the original Q131b bound with coefficients 1+4r^2/(1-r^2) and 8/[r^2(1-r^2)]. Otherwise d_a(u)<=4<=16d_a(g)/a0^2. Consequently throughout the full model

    d_a(u)<=Ccomp[d_a(g)+Lgain],
    Delta(u)=Delta(g)+Lgain,
    Ccomp=max{16/a0^2,1+4r1^2/(1-r1^2),8/[r0^2(1-r1^2)]}.

The constant is independent of n, the number of sorts, and all unregulated features of u. Only the marked sorting gain is used, bounded by the total gain.

## 4. L131: local coercivity without an interior or spike restriction

Orient v=aX_1, put h=u-v, m=Eh, and k=r V(ra)/V(a). For

    G(u)=psi(ra)-I(T_r u)+k[I(u)-psi(a)],

first variations cancel. Its Hessian is

    Q(h)=k[Eh^2/(1-a^2)-m^2]
          -[E(T_rh)^2/(1-r^2a^2)-m^2].

Every nonconstant Walsh coefficient is at least q=k/(1-a^2)-r^2/(1-r^2a^2); the constant coefficient is a^2q. The function f(t)=(1-t^2)V(t)/t has

    f'(t)=[t-(1+t^2)V(t)]/t^2<0.

Hence f(ra)>f(a), exactly equivalent to q>0. Also 0<k<r^2<1. Scalar compactness supplies cH=a0^2 min q>0, and Q(h)>=cH||h||_2^2 uniformly.

The Bregman identity is exact, even at input endpoints:

    G=k E Bpsi(v+h,v)-E Bpsi(rv+T_rh,rv)+(1-k)psi(m).

Take eta<=(1-a1)/2 small enough that D3 eta/6<=cH/8, where D3 bounds |psi'''| on [-(1+a1)/2,(1+a1)/2]. Decompose h=g+b on disjoint supports, with g=h1_(|h|<=eta), b=h1_(|h|>eta). Set p=Pr(|h|>eta)<=||h||_2^2/eta^2. Taylor on the good set and global strong convexity on the bad set give

    k E Bpsi(v+h,v)
      >=k||g||_2^2/[2(1-a^2)]-D3 eta||g||_2^2/6
          +kmin||b||_2^2/2,

where kmin>0 is the compact scalar minimum. No differentiation at ±1 is used.

For qout=min{3,1+r1^(-2)}>2, the output expansion around |rv|<=r1*a1<1 has a uniform remainder bound C_out|T_rh|^qout, valid even when the perturbed value reaches an endpoint. Near zero this follows from an interior third derivative bound; away from zero it follows from bounded continuous psi on its compact domain. Hypercontractivity gives its integral <=C_out||h||_2^qout because 1+(qout-1)r^2<=2.

The required real-function hypercontractivity can also be checked directly, without a Boolean assumption. For 1<p0<=2, let M(t)=E|A+tBX|^p0 and f=M^(2/p0) for a fair sign X. Its second derivative, away from zeros, is a nonnegative square plus

    2(p0-1)B^2 M^(2/p0-1) E|A+tBX|^(p0-2)
       >=2(p0-1)B^2.

The inequality is Jensen for a negative power of |A+tBX|^p0. Continuity and local integrability extend this across zeros; integrating with f'(0)=0 proves ||A+BX||_p0^2>=A^2+(p0-1)B^2. Tensorization with Minkowski and duality give the Lp-to-Lq norm estimates used here.

In particular, with theta=1/(1+r1^2)-1/2>0,

    ||T_r b||_2<=p^theta||b||_2, |Eb|<=sqrt(p)||b||_2.

Use psi(m)>=m^2/2. The good quadratic terms including (1-k)(Eg)^2/2 equal Q(g)/2. The bad output square costs at most Bmax p^(2theta)||b||_2^2/2, Bmax=(1-r1^2a1^2)^(-1). The output and mean cross terms cost at most [Bmax p^theta+sqrt(p)]||g||_2||b||_2. The stated Young bound spends cH||g||_2^2/8 and 2[Bmax p^theta+sqrt(p)]^2||b||_2^2/cH. Choosing p_* so the bad costs are <=kmin/4 and then epsilon_* so p<=p_* and C_out||h||_2^(qout-2)<=min{cH/4,kmin/4}/2 proves

    I(u)=psi(a), ||u-s aX_i||_2<=epsilon_*
       ==> Delta_r(u)>=c_*||u-s aX_i||_2^2.       (L131)

This reproduces the existing proof and constants' scope. All choices depend only on endpoints. The decomposition changes no kernel or information. Small support, large amplitude, arbitrary mean and initial endpoints are included.

## 5. J290, M290 and P290: global entrance at a marked singleton

For a pair law mu of (A,B) on [-1,1]^2 with Ec<infinity and delta=(EA-EB)/2>0, finite cost excludes zero child entropy moments and endpoint means. Indeed if H(A)=0 almost surely, A is an endpoint almost surely and finite cost forces B=A almost surely, contradicting separation. The other entropy and both means are handled identically. Hence the source joining and common-budget optimizer hypotheses are physical, including possible mass at the equal corners.

Define m=(EA+EB)/2, e=(EH(A)+EH(B))/2, Jinfo=H(m)-e, child informations J_A,J_B, and the joining surplus

    Jjoin=Ec+[Phi_(EA)(J_A)+Phi_(EB)(J_B)]/2-Phi_m(Jinfo).

The stipulated joining theorem gives Jjoin>=0. Independently, its equality classification is exactly the point mass at (t,-t), 0<t<1, as follows.

For a reserve parent, including ties, original-child pooling gives Jjoin>=Ec-W(parent)>=Kcost-W(parent). Let the canonical optimizer have interior-core mass k>0, half separation delta_c, and corner masses pi_plus,pi_minus. Parent delta=k delta_c. Put c0=2-4L^2>0. The actual source corner Euler margin is

    tau W'-W>=c0 kappa_tau>=c0 tau^2 delta_c^2/8.

Thus integrating (W/tau)' from tau to 1 retains loss >=c0 tau(1-tau)delta_c^2/8. Compose the positive and negative corner retentions tau1=k/(k+pi_plus), tau2=k+pi_plus; the second ray has separation tau1 delta_c. The retained total loss is

    k W(core)-W(parent)
      >=(c0/8)delta_c^2[k pi_plus+k^2 pi_minus]/(k+pi_plus)
      >=(c0/8)(1-k)delta^2.

Both retentions are positive and include value one when a corner is absent. There is no division by delta. Since Kcost>=k W(core), equality forces k=1. This core is deterministic. If its center m_c is nonzero, the positive entropy series gives Lm_c^2-psi(m_c)>0. The reserve argument L-e_c/(1-m_c^2) is strictly below the positive J_c/(1-m_c^2)<L. Strict increase of S on positive arguments and its zero extension below zero imply

    W(core)<(1-m_c^2)F(J_c/(1-m_c^2))<=c(core).

So equality forces m_c=0. Equality also forces Ec=Kcost; unique priced optimality at the same exact common entropy then forces the actual law, not just its moments, to be that canonical deterministic reflected pair. The capacity case has price zero and the same uniqueness.

For a strict F parent, mean zero is impossible since B_0=F. Reflect to m>0 and orient children. Original-child F pooling gives Jjoin>=Ec-[F(Jinfo)-F(j)]>=Kcost-[F(Jinfo)-F(j)], j=(J_A+J_B)/2. The source high-information comparison makes Jinfo<L/2. In one-positive-corner geometry the core center is nonnegative, so the actual thinning derivative/window margin integrates to

    kF(J_c)-[F(Jinfo)-F(j)]>=c0 k(1-k)delta_c^2/8.

This is strict for k<1. At k=1, center m>0 and strict convexity of F give c(core)>F(J_c) via the deterministic capacity inequality. In reflected-core geometry m>0 forces k<1. Move the common mean to the one-corner wall, preserving mass, separation, entropy and cost. The states stay physical and their information decreases from below L/2. The stipulated wall monotonicity bounds the old demand by the wall demand, where the retained thinning loss is strictly positive, including the transition and zero-length wall motion. Thus equality is impossible in a strict F parent. Conversely a deterministic reflected pair has zero child informations, Phi_0=F, and cost tV(t)=F(psi(t)), so Jjoin=0. This proves J290, with all branch ties and corner cases.

For delta>=b>0, j0<=Jinfo<=j1<L and Ec<=M, laws on the fixed square form a weakly compact set: entropy moments and means are continuous, and the nonnegative lower semicontinuous cost has closed integral sublevels. Within it the preceding argument excludes zero child entropies and endpoint means, hence compactness supplies uniform distances from these excluded states. All profile arguments stay in a compact physical range below L, allowing zero child information, ties and the S seam. Jjoin is lower semicontinuous. The distance

    E[(A-t)^2+(B+t)^2]/2, t=psi^(-1)(Jinfo),

is continuous. Its closed subset at distance >=epsilon has a strictly positive minimum Jjoin by J290; if empty there is no obstruction. This is M290. It is compactness of pair laws on a fixed square, not of growing cubes.

For an interior cube g split at the specified oriented coordinate, the exact energy decomposition and source face production give

    R(g)=[D(g_plus)-Phi_(Eg_plus)(I(g_plus))
           +D(g_minus)-Phi_(Eg_minus)(I(g_minus))]/2
          +Jjoin+Phi_(Eg)(I(g))-F(I(g))>=Jjoin.

Also Ec<=D(g)<=F(j1)+1 if R<=1. The face-law separation is the marked singleton. M290 therefore proves P290: on compact positive information and a fixed singleton lower bound, sufficiently small R forces arbitrarily small L2 distance to the corresponding signed coordinate of amplitude psi^(-1)(I(g)). Dimension-zero constant faces are legitimate, so n=1 is included.

## 6. B290: the complementary fixed singleton sector is fully paid

Fix beta>0. Let an original singleton have magnitude >=beta. Put tmin=-log r1>0, tmax=-log r0 and wmin=psi(r0*a0)>0. P128 implies that, for small enough Delta, every intermediate information is in [wmin/2,psi(a1)]. A time s in the middle third of [0,t] satisfies

    R(s)<=3 exp(K tmax) Delta/tmin.

The original marked singleton at that time remains >=r0 beta, and P_su is interior. P290 puts it as close as desired to the signed coordinate with amplitude psi^(-1)(I(P_su)). On this positive compact information range, psi^(-1) is Lipschitz; P128 makes that amplitude within O(Delta) of a exp(-s). Choose the desired tolerance so E131 at lambda=exp(-s)>=r0 enters the L131 neighborhood of the *original* kernel. Choose the P290 surplus tolerance and then the terminal Delta threshold. L131 gives the linear bound there. Above that fixed positive threshold use d_a<=4. Thus

    max_i |uhat(i)|>=beta ==> d_a(u)<=C_beta Delta_r(u),

with C_beta depending only on beta and endpoints. Every entrance premise is derived. Bias, arbitrary remaining coordinates, corner mass and original spikes are permitted. Neither an unproved coordinate-selection claim nor inverse-noise continuity is involved.

## 7. U300, I301's precise scope, and the full Gaussian gap

I301 passes every measurable scalar w:R->[-1,1] with 0<I_G(w)<L, every 0<sigma<1, and arbitrary bias/endpoints/tails. It also verifies the non-strict interface and the law-preserving rearrangement/compactness implication to G290 on *all* compact open rectangles. These are the exact interfaces required here. I independently checked the following critical mathematics against I300 and I301.

The non-strict Gaussian inequality is derived from the stipulated cube theorem. For smooth bounded v with bounded third derivative apply v to a normalized M-bit block sum. Given the entire noisy output y, centered input summands have conditional means zero, variance (1-sigma^2)/M and third absolute moments O(M^(-3/2)). Second-order Taylor replacement with Gaussians gives a uniform-in-y conditional-mean error O(M^(-1/2)). The centering shift sigma S_M(y) does not affect the bounded derivative estimate. Ordinary output CLT and uniform continuity of psi transfer output entropy and mean; input entropy and mean converge too. Gaussian L2 smoothing approximation and OU contraction extend to all measurable bounded fields. This proves I_G(Q_sigma w)<=f_sigma(I_G(w)), f_sigma(J)=psi(sigma psi^(-1)(J)), for every perturbation needed by the variational argument. No stability assertion is used, and a bare joint weak CLT is not substituted for conditional entropy convergence.

For a,sigma in (0,1), set k=sigma V(sigma a)/V(a) and b=exp(psi(a))-1. I300's crucial strict inequality is

    k>sigma^2(1-b)/(1-sigma^2 b).

The function K(a)=psi(a)+log[a+(1-a^2)V(a)]-log(2a) has zero limits at 0 and 1. Its derivative numerator at a=tanh t is 1-t coth t+t^2 sech^2t. The actual DLMF partial fraction gives

    (t coth t-1)/(t^2 sech^2t)
       =2 sum_(n>=1) cosh^2t/(t^2+pi^2 n^2).

Each summand increases strictly by tanh t>t/(1+t^2); local uniform convergence holds. The ratio starts at 1/3 and diverges, so K first increases then decreases to zero and is positive inside. This proves b>M(a), M(a)=[a/(1-a^2)-V(a)]/[a/(1-a^2)+V(a)]. The coefficient ratios in M(z)/z^2 increase strictly. Therefore for F0(x)=V(a sqrt(x))/(a sqrt(x)),

    F0'/(F0+xF0')=M(a sqrt(x))/x<=M(a)<b.

The essential 1/x is present. Decrease of (1-bx)F0(x) proves the displayed strict inequality. Also 0<k<sigma^2<1 and f_sigma''<0, since aV'(a)/V(a)=sinh(2V(a))/(2V(a)) increases.

With m=Ew and q=Var(w)/(1-m^2), the correctly biased likelihood ratio (1+s w)/(1+s m) gives by joint-law Jensen I_G(w)<=log(1+q). Thus q>=b. Endpoints use the continuous zero extension of R log R; m is interior by positive information.

For a prior-smoothed kernel w=Q_tau u, both 1±w have Gaussian quadratic lower bounds. V(w) has quadratic value growth, w' and w'' are bounded, the Fisher integrand w'^2/(1-w^2) is bounded, and (V(w))' has linear growth. The latter follows from the entropy bound on the tilted Gaussian score; it is a bound for the composed derivative, not for bare V'. A compact additive phi satisfies |phi|<=C(1±w), hence |Q_sigma phi|<=C(1±Q_sigma w), controlling output endpoints as well. First variation at an equality case gives exactly

    Q_sigma V(Q_sigma w)=kV(w)+(1-k)V(m).

There is no free multiplier. Differentiation and self-adjointness, justified by the preceding growth bounds, give

    sigma^2 E[(Q_sigma w')^2/(1-(Q_sigma w)^2)]=kD,
    D=E[w'^2/(1-w^2)]>0.

Both factors of sigma are required. Along w_c(x)=w(x+c), the output equals (Q_sigma w)(x+c/sigma). Euler cancellation of the w'' terms yields

    G''(0)=kD+f_sigma''(I_G(w))A^2
          -E[(Q_sigma w')^2/(1-(Q_sigma w)^2)]
          +(1-k)(Ew')^2/(1-m^2).

The mean sign is positive. Translation differentiability follows either from Gaussian change of variables with bounded entropy integrands or from the controlled Fisher and derivative bounds, including shifted tails. Cauchy–Schwarz and q>=b give

    G''(0)<=D[k(1-sigma^(-2))+(1-k)(1-b)]<0,

contradicting the global minimum furnished by the non-strict inequality. For a merely measurable equality case split sigma=s tau with sigma<tau<1; f_s composed with f_tau=f_sigma and strict monotonicity force equality at the positively smoothed Q_tau w. Its information lies strictly between 0 and L, so the preceding contradiction applies. This removes smoothing without analyticity. Thus U300 passes with precisely its original scope and all endpoint/regularity operations.

For completeness, the law-preserving rearrangement also checks directly. The primary positive-correlation two-set Borell theorem has parallel halfspaces of the same orientation. Its Hessian and the joint OU generator give the correct nonnegative semigroup derivative; interior regularization and bounded-continuous endpoint limits include indicators. For f=(1+v)/2 take its increasing scalar quantile f*. It preserves its full law, including atoms. Layer cake and Borell compare every output-set integral with that over the upper ray of the same measure; all input rays are actual nested level sets of this one f*. Q_sigma f* is increasing. Largest-set integrals and the identity E(W-c)_+=sup_p[M_W(p)-cp] give convex order, hence I_G(Q_sigma v)<=I_G(Q_sigma(2f*-1)). Means and exact input information are preserved.

Bounded monotone scalar kernels are compact in Gaussian L2 by rational diagonal selection, convergence at all continuity points of a monotone limit, and dominated convergence. Bounded-field information is L2-continuous; contraction plus Hermite expansion proves joint OU continuity in field and correlation. Thus exact information I_G(w)=psi(b) on any compact b/sigma rectangle inside (0,1)^2 defines a compact feasible set, nonempty by w=b sign(x). U300 makes its continuous deficit positive everywhere, so its minimum etaG is positive. Rearrangement transfers it to every Gaussian dimension:

    I_G(v)=psi(b) ==> I_G(Q_sigma v)<=psi(sigma b)-etaG. (G302)

This is a fixed scalar compact set, not compactness of growing Gaussian spaces. It covers arbitrary fields, bias and input endpoints. No EPI, small-amplitude threshold, posterior Poincare inequality or trajectory analyticity is a premise. Constants need not remain bounded as parameters approach 0 or 1 outside the chosen rectangle.

## 8. Unrestricted diffuse exclusion: both budgets and every order of limits

Suppose increasing g_k have exact I(g_k)=psi(a_k), a_k,r_k in the original rectangle, Delta_k->0 and alpha_k=max_i ghat_k(i)->0. Choose any fixed r1<lambda<1. Put h_k=T_lambda g_k and sigma_k=r_k/lambda. Their correlations lie in [r0/lambda,r1/lambda] inside (0,1), and lambda*a_k lies in [lambda*a0,lambda*a1] inside (0,1). No lambda*a1<1/sqrt(2) condition is used. Since -log lambda is an earlier noise time, Section 2 gives

    I(h_k)=psi(lambda*a_k)+o(1),
    I(T_(sigma_k)h_k)=psi(r_k*a_k)+o(1).

For fixed degree d, let p_k be the degree-d truncation of h_k and q_k its further-noised polynomial. On cube and Gaussian space its squared L2 norm is the same and <=1, since multilinear monomials have identical orthogonal second moments. Parseval gives cube squared truncation tail <=lambda^(2(d+1)). Gaussian Q_sigma p=q exactly by multilinearity. Monotonicity and boundedness imply 0<=partial_i h_k<=1, so

    Inf_i(p_k)<=E(partial_i h_k)^2<=E partial_i h_k
                 =lambda ghat_k(i)<=alpha_k,
    sum_i Inf_i(p_k)<=d.

The same holds for q_k. These are actual L2 influences, with no Boolean identity.

For C4 tests with bounded fourth derivative, replacing one bit by one Gaussian in p=A+x_iB has fourth-order error <=C||test^(4)||_infinity E B^4 because the first three moments match. On any mixed product of these variables,

    E(A+XB/sqrt(3))^4
      =A^4+2A^2B^2+(EX^4/9)B^4<=(A^2+B^2)^2.

Iteration with Minkowski gives the mixed L2-to-L4 norm bound; undoing the degree weights gives E B^4<=9^(d-1)(Inf_i p)^2. Summation costs <=C_d d||test^(4)||_infinity alpha_k->0. The constants depend on fixed d, not dimension. There is no assertion at degree increasing with k.

Smooth uniform approximation transfers bounded uniformly continuous tests clip and psi composed with clip. The unbounded test dist(x,[-1,1])^2 is legitimate too: compactly supported mollification at a fixed radius tau has bounded fourth derivative, and approximation error <=C tau(1+|x|)+C tau^2. The equal second-moment bound pays it on both spaces. Fix d and tau, send k large, then tau small. On the cube distance to the interval is bounded by |p_k-h_k|. Thus v_k=clip(p_k) on Gaussian space satisfies

    ||v_k-p_k||_(2,G)^2<=lambda^(2(d+1))+o_k(1),
    ||Q_(sigma_k)v_k-clip(q_k)||_(2,G)<=||v_k-p_k||_(2,G).

The second line uses projection toward a bounded field and OU contraction. Corresponding clipped cube polynomials are close to h_k and T_(sigma_k)h_k. Uniform continuity of psi on [-1,1] converts these L2 errors to entropy errors, with an error split bounded by its modulus plus L||error||_2^2/delta^2. Means converge by L2 and scalar continuity of psi. Hence for each zeta>0, first choose d depending only on zeta and fixed lambda, then k sufficiently large, to obtain

    |I_G(v_k)-I(h_k)|<zeta,
    |I_G(Q_(sigma_k)v_k)-I(T_(sigma_k)h_k)|<zeta.

Choose a compact b interval strictly containing [lambda*a0,lambda*a1] and still inside (0,1). Obtain etaG for this interval and the fixed sigma interval *before* selecting errors. Define b_k=psi^(-1)(I_G(v_k)); for small enough errors it belongs to this interval and the Gaussian information budget is exact. Uniform continuity of (sigma,J)->psi(sigma psi^(-1)(J)) on this compact domain makes psi(sigma_k b_k) close to psi(r_k a_k). Choose zeta and the large-k ODE errors so that the two transfer errors and this scalar error total <etaG/2. Applying G302 contradicts Delta_k->0. Both budgets, including bias corrections, have been transferred. There is no loss hidden in clipping or polynomial tails.

## 9. Full linear conclusion and all boundary cases

Absence of such a diffuse sequence implies some beta,eta>0, depending only on the endpoints, with max singleton<=beta ==> Delta>=eta for increasing exact-information kernels. Otherwise choosing beta=eta=1/k produces exactly the excluded sequence, allowing arbitrary dimensions and parameters in the same rectangle. There is no extra uniformity assumption in this extraction. In that sector d_a<=4<=4Delta/eta. In the complementary sector B290 supplies C_beta. Thus Cinc=max{4/eta,C_beta} works for all increasing kernels. Section 3 then gives

    d_a(u)<=Ccomp[d_a(g)+Lgain]
             <=Ccomp max{Cinc,1} Delta_r(u).

Every constant was selected from endpoint-dependent compact scalar ranges, a fixed-square pair-law compactness statement, the fixed lambda, or a fixed local tolerance. None depends on n, bias, support, spike mass, initial endpoint margin, original degree or complexity.

Closed rectangle endpoints and singleton intervals a0=a1 or r0=r1 are included. n=1 has legitimate dimension-zero faces; no part requires two coordinates. Delta=0 causes no division by zero: the diffuse gap excludes its diffuse sector and B290 plus compression force d_a=0. Time selection at zero integrated surplus is still legitimate. Arbitrary original endpoints are addressed at positive time and by L131, and rare spikes are paid by the support/hypercontractive local argument. No balance or hidden regularity premise has entered. The auxiliary Gaussian amplitudes are defined from exact information; initial cube amplitudes are never changed.

## 10. Separate supporting sharpness audit

The parent sharpness note is correct unchanged and is not another finding. Fix any interior pair a,r and n=2. The analytic implicit equation

    [psi(c+epsilon)+psi(c-epsilon)]/2=psi(a)

has derivative V(a)>0 in c at (a,0). It defines an even analytic c(epsilon)>0 with

    c=a-epsilon^2/[2(1-a^2)V(a)]+O(epsilon^4).

For small epsilon, c+|epsilon|<1. Then u=cX_1+epsilon X_2 is balanced, bounded, and has exactly I(u)=psi(a). Since c>|epsilon|, its closest signed coordinate is aX_1, and d_a=(c-a)^2+epsilon^2=epsilon^2+O(epsilon^4). Noise multiplies both singleton coefficients by r; expansion gives

    Delta=K(a,r)epsilon^2+O(epsilon^4),
    K=[rV(ra)/((1-a^2)V(a))-r^2/(1-r^2a^2)]/2=q(a,r)/2>0.

The coefficient equals half the I128/I131 nonconstant Hessian gap, already checked in Section 4. Its positivity also follows from the parent note's exact derivative of (1-t^2)V(t)/t. Therefore for p>1,

    d_a/Delta^p ~ K(a,r)^(-p)|epsilon|^(2-2p)->infinity.

Even one fixed interior parameter pair and n=2 defeats any finite constant with exponent p>1. This proves the claimed sharpness of the exponent in squared L2 distance (equivalently one half for L2 norm). No uniform Taylor remainder over a rectangle is needed for this obstruction. It neither proves the upper bound by itself nor changes its verdict or the count.

## 11. Objections, explanatory expansions and limits

All suspected full-target gaps were checked: retained losses in both joining branches; pair-law profile continuity at child information zero and branch ties; original-budget backward entrance; real rather than Boolean hypercontractivity; spike/endpoints in local Taylor bounds; matching three moments and unbounded clipping-distance transfer; exact Gaussian information and error ordering; law-preserving rather than Boolean rearrangement; uniform gap from fixed scalar compactness; arbitrary lambda in (r1,1); and the logical beta/eta extraction. I301's mean signs, two correlation factors, output perturbation comparability, Fisher finiteness, shifted domination and removal of smoothing cover the required regularity passages. No circularity remains: Gaussian non-strict contraction comes from cube contraction, not S302 or a desired stability theorem.

No repair is required. The detailed derivations here expand valid frozen steps; no missing claim was replaced, no hypothesis was added, and the frozen S302 analysis was not altered. There is no counterexample or exact missing operation left under the stipulated source results. Validation is analytic and by source/byte authentication, not a formal checker or numerical evidence. No numerical scan, subagent, unrelated history replay, live sibling read, shared-index edit, staging, commit, publishing, contribution assessment or acceptance/count change occurred. Only the five assigned I304 files are written, with detached output hashes.
