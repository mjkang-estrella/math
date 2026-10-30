# Author proof of the unchanged r162bm statement

This is a complete author argument relative to the stipulated operative proofs of Source146 at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. It is not an independent correctness or contribution review. STATEMENT.md is the sole frozen assertion. All logarithms below are natural except log_M. Constants denoted C can change; they are independent of the varying map parameter and physical time unless a dependence is explicitly allowed. We never assume ergodicity of area.

## 1. Original cocycle and the one-step mean

Write K=2 pi k and M=K+4. Use the source's fixed area-preserving torus automorphism (x,y) -> (q_0,q_{-1})=(x,x-y). The same original orbit then obeys

    q_{i+1}=2q_i+k sin(2 pi q_i)-q_{i-1} (mod 1),
    A_i=A(v_i),  A(v)=[[v,-1],[1,0]],  v_i=2+K cos(2 pi q_i).

Products T_{i,j}, their inverse convention, and Euclidean operator norms are exactly those of source setup.tex. Define g(i,j)=log_M ||T_{i,j}||. The source's determinant-one and submultiplicative estimates give a stationary symmetric semimetric with 0<=g(i,j)<=|j-i|. Expectations are ALWAYS over normalized original area m. In particular each q_i is uniform; no assertion of independence of different q_i is made.

The norm of one step is

    s(v)=||A(v)||=(sqrt(v^2+4)+|v|)/2,
    log s(v)=asinh(|v|/2).

This follows by diagonalizing A(v)^t A(v), whose determinant is 1 and trace v^2+2. Put

    B_K=integral_0^1 log s(2+K cos(2 pi x)) dx,
    a_i=1-log_M s(v_i),  b_K=E a_0,  zeta_K=E a_0^2.

Here 0<=a_i<=1, since s(v)<=|v|+1<=K+3<M. We will use

    B_K=log(K/2)+O(K^(-1)),
    b_K=O(1/log M),  zeta_K=O((log M)^(-2)).                 (1)

Proof of (1): for K>2, factor 2+K cos t as (K/(2z))(z^2+(4/K)z+1), |z|=1. Both roots of the quadratic have modulus one. The integrable circle logarithm of each factor z-r has mean zero, giving integral log|2+K cos t|=log(K/2). This elementary identity also follows by integrating log(2|sin(t/2)|); isolated zeros cause no problem. The nonnegative difference

    R(v)=log s(v)-log|v|

is integrable on the real line: it is O(1+|log|v||) at zero and O(v^(-2)) at infinity. The law of v has density [pi sqrt(K^2-(v-2)^2)]^(-1) on (2-K,2+K). For K>=8 this density is <=C/K on |v|<=K/2, while R<=C/K^2 outside that interval. This proves the first estimate. For the second moment let L(v)=log M-log s(v). On |v|<1 its squared integral is <=C(log M)^2/K. On 1<=|v|<=K/2 use 0<=L(v)<=log(M/|v|), so the integral is bounded by C K^(-1) integral_1^{K/2} log(M/r)^2 dr<=C. On the complement L is bounded by an absolute constant. Thus E L(v)^2<=C; dividing by (log M)^2 gives the last claim. The mean claim follows either from this or the first estimate.

By Oseledets and bounded convergence for this fixed smooth cocycle,

    lim_n n^(-1) E log||T_{0,n}|| = integral lambda_+(f_k) dm.

The fixed linear conjugacy does not alter that limit (its contribution is bounded independently of n). The entropy formula for a C^(1+alpha) diffeomorphism preserving absolutely continuous probability on a compact manifold gives this integral equal to h_m(f_k). It applies also when exponents vanish and when m is not ergodic. Source main:pesin supplies this interface; the actual Mane proof and its errata were additionally read. Submultiplicativity and stationarity give h_m(f_k)<=B_K. It remains to prove

    B_K-h_m(f_k) -> 0.                                    (2)

## 2. Compensation, initial scales, and critical-scale selection

Define the additive nonnegative line semimetric

    c(i,j)=sum_{r=i}^{j-1} a_r  (i<j), c(j,i)=c(i,j),
    d(i,j)=g(i,j)+c(i,j).

Although c is additive on ordered triples, no tree inequality is claimed for d at finite K. The sum d is a stationary semimetric and satisfies d(i,j)<=|j-i|, because log||T_{i,j}||<=sum log||A_r||. In fact d(i,i+1)=1. Define

    t_n=E[1-d(0,n)/n]=e_n-b_K,
    D_K=(B_K-h_m(f_k))/log M.

The numbers t_n are nonnegative, tend to D_K, and are nondecreasing along dyadic lengths. Every aligned triangle loss of d is IDENTICAL to that of g. Source scale:doubling consequently implies

    t_n<=t_{2n}<=C t_n+(C-1)b_K+C/n.                       (3)

We need a more accurate INITIAL estimate than (3). Let E_n be the event |v_i|>=sqrt K for 0<=i<n. Uniform individual marginals and a union bound give m(E_n^c)<=C n/sqrt K. On E_n, start u_{-1}=0,u_0=1 and u_{i+1}=v_i u_i-u_{i-1}. Induction gives |u_{i-1}/u_i|<=2/sqrt K and hence

    log|u_n| >= sum_{i=0}^{n-1} log|v_i|-4n/K.

Indeed each factor differs from |v_i| by relative error <=2/K, and log(1-2/K)>=-4/K for large K. Since ||T||>=1 everywhere and sum log|v_i|<=n log(K+2), integration, including the possibly negative values on E_n^c, yields

    E log||T_{0,n}|| >= n log(K/2)-4n/K
                          -C n^2 log(K+2)/sqrt K.

Combining this with (1) gives, for every n>=1,

    0<=t_n<=C/(K log M)+C n/sqrt K.                        (4)

Suppose (2) fails. There then exist one eta>0 and a sequence K->infinity with B_K-h_m(f_k)>=eta. Fix that eta for the remainder of the contradiction. Choose n_0 the largest power of two not exceeding K^(1/4) and theta=eta/(2 log M). By (4), t_{n_0}=o(theta), whereas D_K>=2theta. Let N be the FIRST dyadic length at least n_0 with t_N>theta, and put epsilon=t_N. For large K, N>n_0. Equation (3) applied once at N/2, with (1), gives

    eta/(2 log M)<epsilon<=C_eta/(log M),
    epsilon->0, n_0->infinity, epsilon n_0->infinity,
    zeta_K/epsilon ->0.                                  (5)

For every fixed integer m, all eventually integral dyadic shifts satisfy

    t_{2^m n_0}=o(epsilon),    t_{2^m N}=O_{m,eta}(epsilon). (6)

The first assertion follows directly from (4), including positive m; it does NOT follow by discarding b_K in (3). For nonnegative terminal shifts iterate (3), using b_K=O_eta(epsilon); for negative shifts use dyadic monotonicity. These are precisely the critical-scale boundary bounds required below. All scale sums from here to the end are n=n_0,2n_0,...,N/2 unless otherwise specified.

## 3. Joint weighted estimates for the physical additive clock

For dyadic s<t set

    d_n(s,t)=d(floor(ns),floor(nt))/n,
    c_n(s,t)=c(floor(ns),floor(nt))/n.

Both belong to the source compact space X of symmetric semimetrics bounded by |s-t|+2. For a fixed interval I=[s,t] of power-of-two length p, eventually all endpoints and half-endpoints align at every scale in the sum. Write

    H_I=1-d_n(s,t)/p,    A_I=c_n(s,t)/p,
    J_I=H_I-(H_{I_l}+H_{I_r})/2,
    V_I=(H_{I_l}-H_{I_r})^2,    W_I=J_I+V_I.

On these samples 0<=H_I,A_I<=1 and J_I,V_I>=0. Clock additivity is the exact relation A_I=(A_{I_l}+A_{I_r})/2. These are physical intervals of the original orbit; no random time change is being made.

Stationarity gives E H_I=t_{pn}, E J_I=t_{pn}-t_{pn/2}. The exact telescope and (6) imply

    sum_n E J_I= t_{pN/2}-t_{pn_0/2}=O_I(epsilon).

If Hbar=(H_l+H_r)/2, then H=Hbar+J and

    V/4=(H_l^2+H_r^2)/2-Hbar^2
        <=(H_l^2+H_r^2)/2-H^2+2J.

The squared terms telescope after expectation, by stationarity. Their initial boundary is at most t_{pn_0/2}=o(epsilon), and their terminal boundary is nonpositive. Therefore

    sum_n E W_I=O_I(epsilon).                             (7)

The same calculation also yields E(H_I+W_I)=O_I(epsilon) at each scale n<=N, and o(epsilon) at n_0. Constants may depend on eta and the fixed interval, not on K or on the number of scales.

Clock averages have E A_I^2<=zeta_K by convexity, without independence. With Delta A=A_l-A_r, exact harmonicity gives

    (Delta A)^2/4=(A_l^2+A_r^2)/2-A^2.

Summing expectations telescopes and proves

    sum_n E(Delta A_I)^2 <=4 zeta_K.                      (8)

There are TWO necessary joint estimates, not merely (7) and (8) separately. Put Delta H=H_l-H_r. The exact product identity is

    H A=(H_l A_l+H_r A_r)/2 + J A - Delta H Delta A/4.

After summing expectations, the positive terminal boundary is at most
sqrt(E H_terminal^2 E A_terminal^2)<=C_I sqrt(epsilon zeta_K), while the negative initial boundary may be dropped. Equations (7),(8) and Cauchy--Schwarz give

    sum_n E A_I J_I <= C_I sqrt(epsilon zeta_K).           (9)

Multiplying the squared-shortfall inequality by A, and using

    A(H_l^2+H_r^2)/2
       =(A_l H_l^2+A_r H_r^2)/2
          -Delta A (H_l^2-H_r^2)/4,
    |H_l^2-H_r^2|<=2|Delta H|,

gives

    sum_n E A_I V_I
       <=4 E[A_initial H_initial^2]
          +8 sum_n E A_I J_I
          +2 sqrt((sum_n E(Delta A)^2)(sum_n E V_I))
       =o(epsilon)+O_I(sqrt(epsilon zeta_K))=o(epsilon).  (10)

The initial term is <=E H_initial=o(epsilon), and (5) is used only in the final equality.

We must also control a clock interval DIFFERENT from the shortfall-test interval. For any two fixed dyadic intervals I,I' of power-of-two length,

    sum_n E(A_I-A_{I'})^2 <= C_{I,I'} zeta_K.              (11)

Here is a finite deterministic proof. Choose one dyadic interval Q of power-of-two length containing both, with a finite dyadic subdivision fine enough that both I and I' are unions of its leaf intervals. Each average is the corresponding convex combination of leaf averages. Their difference has coefficients of sum zero, and so is a fixed linear combination of the differences between child averages at the internal vertices of this finite binary subdivision tree. Cauchy--Schwarz bounds its square by a constant times the sum of those finitely many child-difference squares. Every vertex interval has fixed dyadic endpoints and power-of-two length, so (8), with stationarity at its location, applies. This proves (11). Q can cross zero (take Q=[-2^r,2^r]); no special anchored grid assumption is needed.

Since 0<=W_I<=2, W_I^2<=2W_I. Equations (7),(9)--(11) give the crucial crossed estimate

    sum_n E[W_I A_{I'}]
      <=sum_n E[W_I A_I]
          +sqrt((sum_n E W_I^2)(sum_n E(A_{I'}-A_I)^2))
      =o(epsilon).                                     (12)

This estimate is simultaneous for each fixed pair of tests after a countable diagonal extraction. It allows any finite collection of such pairs, with constants fixed before K grows. The mean b_K/epsilon need not tend to zero and is never assumed to do so. The vanishing ratio is zeta_K/epsilon, combined with (12).

## 4. Joint compact limits, including weighted mass at affine arrays

Let Acal={d_w(s,t)=w|s-t|:0<=w<=1}, U=X\Acal. On the compact product X x X take pairs (d_n,c_n), and on U x X define

    mu_K=epsilon^(-1) sum_n Law(d_n,c_n),
    nu_K=epsilon^(-1) Law(d_N,c_N),
    xi_K=epsilon^(-1) Law(d_{n_0},c_{n_0}).

Source scale:affinity-tests applies to the FIRST coordinate: the common zero set of the W_I is Acal. Its proof uses only semimetric inequalities and dyadic subdivision, both available here. A compact subset of U x X is consequently bounded below by a positive finite sum of W_I. Equation (7) and its single-scale counterparts give local boundedness, vague subsequential limits mu,nu, and xi_K->0. One may use exactly the compact cutoffs dist(d,Acal) from source scale:limits, now independent of the second coordinate.

These limits have c=0. For nu, E A_I^2/epsilon<=zeta_K/epsilon->0; hence any fixed positive clock value has zero mass on each compact set in the limit. For mu, on a compact first-coordinate set F away from Acal choose sum_{j<=r} W_{I_j}>=c_F. If A_{I'}>=u>0, its prelimit mass over F is bounded by (c_F u epsilon)^(-1) sum_{j,n} E[W_{I_j}A_{I'}], which tends to zero by (12). Testing with compact cutoffs and then taking the countable union over I', positive rational u, and compact exhaustions proves the assertion. Vanishing on all dyadic intervals of power-of-two length forces c=0 everywhere by its nonnegativity and the semimetric triangle inequality (any pair is contained in one such interval).

A stronger statement is needed for affine leakage. For each fixed I, the positive finite measures J_I mu_K,V_I mu_K on the ENTIRE compact product have uniformly bounded mass. Every weak limit of either is supported on c=0, since (12) gives integral A_{I'} W_I dmu_K->0 for every I'. The limit clock is nonnegative and additive on all ordered dyadic triples: this is a closed condition satisfied eventually on every finite aligned triple. Thus the preceding countable test argument applies also to these finite weighted measures. If a continuous weight G obeys |G|<=C W_I, all weak signed limits of G mu_K are supported on c=0 as well. This is stronger than vague disappearance away from affinity.

At finite scales g_n=d_n-c_n is the ORIGINAL matrix distance array. Its four-point estimate is source scale:fourpoint with C_0=6. After log_M and division by n it has error <=C/n_0. On any fixed strict violation of that inequality by d-c, samples are absent for large K. This observation, tested locally, passes the inequality to limits despite their possibly unbounded total masses. Since c=0 on mu and nu, their first coordinates satisfy

    d(s,t)<=|s-t|,
    B_v(s,t)>=min(B_v(s,p),B_v(p,t)),
    B_v(s,t)=d(v,s)+d(v,t)-d(s,t).                        (13)

No four-point theorem for the finite compensated array was invoked. The first inequality and the semimetric triangle inequality give joint Lipschitz continuity, so (13) extends uniquely from dyadic to all real arguments. This is the source class X_0.

Fixed dyadic translation invariance passes to the joint limits by exact stationarity once nr is integral. Apply dilation S to both coordinates, S d(s,t)=d(2s,2t)/2. Floor conventions give S(d_n,c_n)=(d_{2n},c_{2n}) exactly. Hence

    S_* mu_K=mu_K+nu_K-xi_K.

S is proper on U x X: the inverse image of the affine FIRST-coordinate set is itself, and inverse images of compacts are closed in the ambient compact product. Passing to vague limits gives S_*mu=mu+nu. On their support (d,0) with d in X_0, S is invertible with inverse 2d(s/2,t/2). The source's positive local subtraction, not a subtraction of infinite total masses, now gives

    mu=mu_infty+sum_{j>=1}(S^(-j))_*nu,                  (14)

where mu_infty is nonnegative, locally finite, dilation invariant and invariant under every dyadic translation. The series is dominated by mu. From now on we suppress the zero second coordinate. We retain globally weighted weak limits on X x X when handling affine leakage.

For every fixed I, integral W_I dmu<infinity and integral(H_I+W_I) dnu<infinity. In particular integral H_[0,1] dnu<=1, because the corresponding terminal prelimit integral equals t_N/epsilon=1.

## 5. Transport of compensated observations along the ORIGINAL bridge

The original source bridge:theorem permits bounded Lipschitz functions of finitely many normalized product shortfalls near either endpoint, on the event g(a,b)>=c_b(b-a). We require the same estimate for bounded Lipschitz functions of compensated shortfalls H. The bridge event remains the ORIGINAL one. Here are the additional estimates needed to repeat the operative proof.

The periodic scalar a(q)=1-log_M||A(2+K cos(2 pi q))|| is globally Lipschitz with constant <=CM (and in fact <=CM/log M). Indeed ||A||>=1, the norm is Lipschitz in its entries, and the entries are CM-Lipschitz in q. Differentiability at v=0 is unnecessary. Suppose two states are on one of the source contracting graphs, with endpoint state-pair separation <=C M^(-.8(B-1)), where B>=n/3 is the distance from its eligible middle to the relevant endpoint. Under up to kappa n forward OR backward iterates this separation is at most C M^(kappa n+O(1)) M^(-.8(B-1)), since each one-step map and inverse has derivative norm <=M in the source coordinates. Every clock average on an interval within that endpoint window therefore changes by at most

    C M^(kappa n+O(1)) M^(-.8(B-1)).                      (15)

There is no factor equal to the number of sites: this is an AVERAGE. If necessary the constant O(1) absorbs the CM Lipschitz factor. The source's product telescoping estimate for the old normalized shortfall is at most

    C M^(3 kappa n+O(1)) M^(-.8(B-1)),                    (16)

uniformly over all nonempty observation intervals in the window. Their difference H=old shortfall minus clock average obeys the sum of (15),(16). Choose fixed smaller positive kappa,sigma if needed so 3kappa+sigma<.8/3. Then bounded Lipschitz observations of finitely many H-values vary by <=C_{R,L,B} M^(-sigma n), with a harmless further reduction of sigma for the O(1) exponent. This choice is independent of K,n,indices, and of a fixed threshold h. All realized H-values lie in [0,1].

Now use the source proof without changing its physical geometry: fast original bridges have a positive proportion of eligible middle indices; each has the two closed endpoint row choices B or B-1, finite Dirichlet graphs of extent 1/4, and uniform partial-derivative distortion. The intercept labels for H>=h remain compact because H is continuous (Lipschitz suffices). The forward label area is <=C m(H>h/2) by (15),(16). At a fixed label the backward transverse sweep has the SAME Jacobian ratio and small-slope injectivity as source bridge:sweep-jacobian. Integrating a nonnegative W on that sweep is <=C(EW+M^(-sigma n)). The local chart argument on compact eligible sets is unchanged, as it concerns the original graphs, not differentiability of W or H. Summing the finitely many squares and row choices, averaging eligible middles, and reversing the two ends if needed proves

    E[1_{g(a,b)>=c_b n} W 1_{H>h}]
        <=C(EW+M^(-sigma n)) m(H>h/2).                   (17)

Here W,H are observations of compensated shortfalls with fixed bounds R,L,B; C and lower thresholds may depend on those bounds and h, but c_b,kappa,sigma are fixed absolute choices. This is a deterministic area-transport estimate, not an independence assumption or a perturbed map assertion.

## 6. Support exclusions and shape geometry

Choose once and for all c_* with c_b<c_*<1. In this section c_* is a SPEED threshold, not the source crossloss constant. Choose delta>0 so 2delta<=delta_can and delta<=delta_can, reducing further to delta<1/100 if needed. Suppose compensated wings of length n satisfy d(i,i+-n)>=(1-delta)n and the whole has d(i-n,i+n)<=delta n. Since g,c>=0 and the clock is additive, each wing clock is <=c(i-n,i+n)<=delta n. Thus original wings are >=(1-2delta)n and the original whole is <=delta n. Source can:theorem applies and bounds this event by C exp(-gamma n). The normalized scale sum epsilon^(-1) sum_n exp(-gamma n) tends to zero by (5). This proves the same forbidden near-total-cancellation support exclusion with threshold delta.

For fixed separated dyadic windows use W_I=J_I+V_I near one end and H_{I'} near the other in (17). Their bounds are fixed. Equation (7) gives sum EW_I=O(epsilon), while (6) and Markov give m(H_{I'}>h/2)<=C_h epsilon uniformly at the scale in question. After division by epsilon, the sum of the right side of (17) is O(epsilon)+o(1). Hence the weighted bridge mass tends to zero. In the JOINT compact space the relevant original-fast open set is

    { (d,c): (d-c)(a,b)>c_b |b-a|, H_{I'}(d)>h }.

All limiting mass has c=0. Thus every limit point with d(a,b)>c_*|b-a| is covered by such an open set. Source shape:exclusions uses countably many dyadic secants, fixed thresholds and the affinity tests to deduce the following statement: if P_d is the set of times at which d is not locally affine and Q_d the set of times at which it is not locally unit-speed, then

    s in P_d, t in Q_d ==> d(s,t)<=c_* |s-t|.             (18)

For completeness, the locality step uses shrinking dyadic neighborhoods about s carrying a positive J or V and about t carrying a positive shortfall. When the connecting secant is strictly faster than c_* their endpoints still give an original-fast bridge after sufficiently small neighborhoods; its two windows fit kappa. Continuity of the tests and a countable rational-margin cover turn zero weighted mass into exclusion of that open configuration. If all J,V vanish in a neighborhood it is affine there by the dyadic subdivision argument; if all shortfalls vanish it is unit-speed there. This is exactly the operative locality argument of the source, now justified by (17) and the joint zero-clock support. The cancellation exclusion holds for mu and nu; nu is also dominated through S_*mu=mu+nu, so weighted exclusions transfer to it after scaling. Equation (18) and the forbidden triples therefore hold for both.

The hypotheses of source shape:classification and shape:crossloss are now all satisfied: continuous semimetric, (13), (18), forbidden matched-wing triples, and nonaffinity. Their proofs are purely geometric on these arrays, independent of the discarded zero-exponent assumption. They give the same three exhaustive shape types:

* all secants have speed at most c_*;
* one exterior exact-unit-speed ray and a slow complementary half-line;
* two exterior exact-unit-speed rays separated by a slow interval [a,b] of strictly positive length L=b-a.

No additivity across the slow interval is asserted. On a two-ray shape the actual source crossing comparison gives

    0<=1-d(z,z+t)/t<=C_cross L/t,  C_cross=2+6/delta,      (19)

and the shortfall is zero for intervals wholly inside either unit ray. This comparison uses the tree inequality, matched ray distances and forbidden triple, not an independent renewal model. All these source operations are credited as inputs; the new work was to recover their hypotheses after compensation.

## 7. Exact cap balance with no affine weighted loss

Choose the source smooth nondecreasing cap Phi on [0,1] with Phi(u)=alpha u near zero, Phi(u)=1 for u>=1-c_*, and alpha>0 so 10 C_cross alpha<1. It may be extended smoothly to R. There are fixed 0<c_Phi<=C_Phi<infinity with c_Phi u<=Phi(u)<=C_Phi u on [0,1]. With H_t(z)=1-d(z,z+t)/t put

    G=Phi(H_2(0))-[Phi(H_1(0))+Phi(H_1(1))]/2.

The elementary second-order Taylor bound is

    |G|<=||Phi'|| J_[0,2]+(||Phi''||/8) V_[0,2].          (20)

Thus G is mu-integrable. Take a subsequence so

    H_Phi=lim_K integral Phi(H_1(0)) dnu_K

exists; c_Phi<=H_Phi<=C_Phi. Exact stationarity and dyadic telescoping give

    integral G dmu_K
       =integral Phi(H_1(0)) dnu_K
         -epsilon^(-1) E Phi(H_1(0;d_{n_0})) -> H_Phi.    (21)

To pass this identity to mu, take simultaneous finite weak limits on X x X of J mu_K,V mu_K,G mu_K, denoted lambda_J,lambda_V,rho. Equation (20) bounds total variation, and Section 4 proves that ALL these weighted limits are supported on c=0, including at affine d. On U x X they equal J mu,V mu,G mu. We show that rho has no mass on Acal x {0}.

For 0<=w<=c_*, all derivatives Phi',Phi'' vanish at 1-w. In shrinking neighborhoods of this compact affine-speed segment, the Taylor estimate improves to |G|<=u(J+V) for arbitrary u>0. Passing to the weak limits and letting u decrease to zero proves zero rho mass there.

For c_*<w<1, fix one large dyadic R with kappa R>2 and use W=J_[0,2]+V_[0,2], H=H_[R,R+1] in (17). For every positive rational h the joint open set

    { (d,c): (d-c)(0,R)>c_b R, H_[R,R+1](d)>h }

has W mu_K mass tending to zero by Section 6. The positive-measure open-set inequality gives zero (lambda_J+lambda_V) mass on it. Every (d_w,0) in the present speed range lies in one such set, because w>c_*>c_b and 1-w>0. The countable cover and (20) exclude this entire intermediate segment. No estimate uniform as w approaches one is needed.

It remains to treat (d_1,0). For a fixed inverse power of two q in (0,1), let the ORIGINAL wings at physical center n be

    D=n-min(g(0,n),g(n,2n)),
    ell=g(0,n)+g(n,2n)-g(0,2n)=2n J(d_n).

Both D/n and ell/n are continuous functions of the pair (d_n,c_n), and vanish at (d_1,0). The inequality 2q-2D/n>ell/n defines an open neighborhood U_q of that pair. With s=qn (integral at all sufficiently large sampled scales), the ORIGINAL source scale:truncation gives ell<=ell_cut+A for its fixed constant A. Clock additivity makes each cancellation loss exactly unchanged under compensation. Thus on U_q

    J_[0,2](d_n)<=q J_[1-q,1+q](d_n)+A/(2n).

The shorter test telescopes:

    integral J_[1-q,1+q] dmu_K
      =(t_{qN}-t_{qn_0})/epsilon<=1.

Also epsilon^(-1) sum_n n^(-1)=O((epsilon n_0)^(-1))=o(1). Consequently lambda_J(U_q)<=q by the open-set inequality. Letting q decrease through inverse powers of two gives lambda_J({(d_1,0)})=0. In a neighborhood of d_1 the cap is linear, so G=alpha J, and rho also has no atom at this pair. The weighted zero-clock support already removed every other point lying over the affine set.

Weak convergence of finite signed measures on the ambient compact space preserves total mass. Equation (21), the agreement on U, and the complete affine analysis establish

    integral G dmu=H_Phi>0.                              (22)

This is where merely showing c=0 vaguely away from Acal would have been insufficient.

## 8. Terminal and invariant contributions, with actual hypotheses

We spell out the source final comparisons to specify the transferred measure interfaces. Positivity in (14) and integrability in (20) give an absolutely convergent decomposition

    integral G dmu = integral G dmu_infty
                       +sum_{j>=1} integral G(S^(-j)d) dnu. (23)

The sum of absolute integrals is bounded by integral |G| dmu. Terminal cutoffs give integral H_1(0) dnu<=1 and integral Phi(H_1(0)) dnu<=H_Phi. Subdivision and stationarity give integral H_{2^(-m)}(0) dnu<=1 for every m>=0. Write A_m=integral Phi(H_{2^(-m)}(0)) dnu. These are finite and bounded. Translation by 2^(-j) gives

    integral G(S^(-j)d) dnu=A_{j-1}-A_j.

Absolute convergence implies A_m converges. Fatou then bounds the terminal series by

    H_Phi - integral liminf_m Phi(H_{2^(-m)}(0)) dnu.

If nu=0 the series is zero, strictly below H_Phi. Otherwise every nonaffine shape in its support has an open slow interval by Section 6. Such an interval contains a dyadic z, and all sufficiently short [z,z+2^(-m)] have capped shortfall one. These measurable eventual-one events, indexed by dyadic z, cover the support. One has positive nu mass; dyadic translation invariance transfers that mass to z=0. The subtracted integral is therefore positive (and finite by Fatou and bounded A_m). Thus

    sum_{j>=1} integral G(S^(-j)d) dnu < H_Phi.            (24)

For the invariant remainder, entirely slow shapes have G=0. On one-ray shapes the finite interface coordinate a or b is measurable by the source's countable secant definitions. Interfaces in a bounded interval force a fixed unit secant on one side and a fixed slow secant on the other. Those two closed tests lie in a compact subset disjoint from affinity, giving finite endpoint intensity. Translation and dilation invariance imply for that intensity lambda

    lambda([0,1))=lambda([0,2))=2lambda([0,1)).

It vanishes, and integer translates show that all one-ray shapes have zero mass.

On the two-ray class restrict mu_infty to 1<=L=b-a<2, calling the restriction mu_*. Its left endpoint intensity is finite on bounded intervals: split those intervals into length-1/4 bins; each bin supplies a fixed slow secant inside [a,b] and a fixed unit secant to its left. This again places the arrays in a compact set away from affinity. The right endpoint intensity is finite as well since 1<=L<2. Dyadic translation invariance excludes atoms. Put I_0=mu_*{0<=a<1}<infinity.

Dilation maps the length bands bijectively; their positive decomposition and |G|-integrability imply

    integral_{two rays} G dmu_infty
        =sum_{j in Z} integral G(S^j d) dmu_*,

with absolute convergence. Let F_j=integral Phi(H_{2^j}(0)) dmu_*. It is finite: (19) says its integrand vanishes unless -2<=a<=2^j. Translation invariance gives each summand F_{j+1}-F_j. At fine scales dominated convergence, using the bounded endpoint window, gives

    F_fine=mu_*{a<0<b}>=I_0.

At coarse scales (19) gives 0<=H_t(0)<=2C_cross/t uniformly on this band. These shortfalls all lie in the linear region of Phi once t is large. The endpoint window has mass (t+2)I_0 for dyadic integer t, so

    F_coarse<=2 alpha C_cross I_0.

The convergent telescoping series is F_coarse-F_fine<=0. This includes I_0=0, when integer translates force mu_*=0. Together with the other two shape types this proves

    integral G dmu_infty<=0.                             (25)

These are precisely source end:terminal and end:remainder at their actual translation, dilation, local-finiteness, shape and crossloss hypotheses; no entropy normalization or finite-parameter zero-exponent assertion enters their proofs.

Equations (22)--(25) give H_Phi=integral G dmu<H_Phi, a contradiction. Therefore there is no sequence K->infinity on which B_K-h_m(f_k)>=eta for any fixed eta>0. The nonnegative difference tends to zero. Equation (1) now proves

    h_m(f_k)=log(K/2)+o(1)=log(pi k)+o(1)

along the full positive real parameter tail, with normalized ORIGINAL area. The sequential contradiction is equivalent to the every-epsilon/every-k quantifiers of STATEMENT.md; no favorable parameter subset has been selected. No rate, effective threshold, ergodicity, full-measure nonzero exponents, perturbation result or alternative forcing is asserted.

## 9. What is supplied and what is newly proved here

Source cancellation, all its degeneracy handling, original finite Dirichlet graphs, both transverse changes of variables, four-point geometry, original truncation, affine detection, positive dilation subtraction, shape classification, crossing loss, and both final cap comparisons are stipulated paid operations. Pesin's formula at absolutely continuous nonergodic hypotheses is also paid. This argument does not audit them.

The added operation is compensation by the ACTUAL orbit's one-step log-norm loss while retaining all original physical bridges and cancellations. Equations (9)--(12) control that clock jointly against the complete multiscale affinity tests, including globally weighted mass at affine arrays. Equations (15)--(17) carry the new observations through the actual source graphs. These justify recovering original tree geometry only AFTER the clock has disappeared, and using the original truncation at unit-speed leakage. The proof does not claim that adding an arbitrary line metric preserves tree geometry, nor that a small average clock is negligible after epsilon^(-1) normalization. It uses zeta/epsilon->0 and the joint telescopes instead.

All author obligations for the frozen scope have been addressed in the argument above. Independent adversarial correctness and a separate actual-primary substantial-contribution judgment remain for the parent to commission and adopt. No review outcome or campaign increment is claimed.
