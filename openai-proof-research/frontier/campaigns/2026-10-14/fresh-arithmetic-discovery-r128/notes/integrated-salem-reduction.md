# Quartic Salem field sums: strongest integrated reduction

**PREFREEZE / no nominee.** This is a research calculation and source-composition comparison, not a frozen new theorem, full author-proof nomination, independent correctness/contribution grade, or count. No source truth audit is performed. The pinned source and its operative proofs are stipulated true. The exact mathematical quantifiers below describe what the composition pays; they are not a replacement for any old full target.

## 1. Inputs read before this derivation

Pinned Source153, `main.tex` and the complete `salem.tex` (445 lines), were read, including `sal:construction`, `sal:loss`, the full phase-window separation proof, and `sal:examples`. The standalone Salem section has no dependency on the other source's classification/non-Pisot/certificate proofs. The classification's exact statement and opening were inspected; its remaining proof and the independent degree31 construction are not claimed read. All six retained TeX/bibliography blobs match their exact canonical paths, sizes and Git blob identities at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

The actual primary Cheng–Fang–Ma–Zhang, arXiv2610.12072v2, 9 October2026, main proof through its conclusion was read: Lemmas2.1/2.3, the quartic classification, trace-dual seeds, mirror proof, controlled returns and final entropy argument. Its predecessor arXiv2610.09902v1, sections4–5, was read for the operative reciprocal/mirror/return proof. The predecessor's positive-torus/collision argument and the quantitative appendices are not used or claimed fully read. These are newer primary dependencies, separate from the stipulated pin.

Bisbas–Neunhäuserer's author-uploaded June25,2009 body, Theorem1.3 and section4, explicitly contains the biased-factor modulus comparison used below. Its full projected-entropy proof and all its transitive antecedents are not being claimed. Peyrière1975, section1.1/Theorem1.2 and its proof, gives the classical phase-separation antecedent. Falconer–Mattila2016, Theorem2.1 and proof, gives the classical finite-energy projection interface used in the contrast calculation; the requested Kaufman1968 publisher PDF returned403. The projection estimate needed here is also proved directly below.

Actual old scopes/proofs read: analyticr11 original sextic scope; complete salem-sextic-r2 candidate; arithmeticr64 exact T153M64 scope and complete markov-transfer; analyticr26 original classification screen. The sextic all-signs target, the all-q symmetric-Markov target, and the retained-root branching question remain unchanged. Nothing below supplies their missing operation. Their historical counts and priority remarks are not adopted.

## 2. The paid conclusion being tested

Fix a quartic Salem number beta in (1,2), put K=Q(beta), fix r>=1, and fix a_1,...,a_r in K. For each row i and each n>=0, let epsilon_(i,n) take values +/-1, with arbitrary prescribed probability p_(i,n) in [0,1]. Assume **all these signs are mutually independent**. Put

    Y = sum_(n>=0) beta^(-n) sum_(i=1)^r a_i epsilon_(i,n).

The series converges absolutely. Zero coefficients may be deleted; if all vanish the law is a point mass.

The integrated argument below gives, for each fixed beta and finite coefficient tuple, a number eta>0, independent of the entire probability array, such that

    dim_H Law(Y) <= 1-eta.

Here dimension is the infimum of dimensions of Borel sets of full measure. The full-measure set may depend on the probabilities. No uniform eta over coefficient tuples or over r is asserted, and no explicit numerical eta is computed. Translation by a fixed real number does not change the conclusion. For a constant fair array this includes every fixed finite convolution of field-scaled copies of the source measure. It includes arbitrary nonstationary independent biases; it does **not** allow Markov dependence, arbitrary correlated finite-alphabet digits, infinitely many coefficient rows, or arbitrary real coefficients.

These are broad quantifiers, but broad quantifiers alone do not identify a new operation. Sections3–8 show exactly why the source plus actual primary proof already supplies them.

## 3. A finite reciprocal family, with denominators paid

Let tau:K->K be the automorphism beta->beta^(-1). It exists since beta^(-1) is a conjugate lying in K and generates K; it has order2. Let sigma:K->C send beta to the nonreal conjugate z, |z|=1. The four embeddings are id,tau,sigma,conjugate(sigma).

Close the nonzero coefficient set under tau, obtaining a finite set B. Choose a positive integer d so that d a is an algebraic integer for every a in B. An integer denominator exists by expressing finitely many coefficients in a rational power basis. Tau preserves integrality, so the same denominator works for the closure.

Use the source products

    A_m = product_(h<=m)(beta^(k_h)-beta^(-k_h)),
    b_m = sum_(h<=m) k_h,
    c_m = product_(h<=m)(z^(k_h)-z^(-k_h)),
    delta_m=|c_m|, L_m=log(1/delta_m).

For a in B define u_(a,m,j)=d a A_m beta^j. These are algebraic integers for every integer j because beta is a unit. Therefore none is a rational half-integer. The exact trace is

    T_(a,m,j)
      = u_(a,m,j) + (-1)^m u_(tau(a),m,-j)
        + 2 Re(d sigma(a)c_m z^j) in Z.                         (3.1)

Reflection is into tau(a), not generally into a. Ignoring this distinction would leave a real compatibility gap. Closing a **finite** coefficient set under tau pays it without a new approximation problem: the same single angle z controls every neutral term, up to fixed constants.

Take C0>=1 larger than all d|a| and d|sigma(a)| for a in B, and put B_m=b_m+log_beta(C0)+1. Then real tails are bounded by beta^(B_m+j), and neutral trace errors by2C0 delta_m. The constant shift from b_m to B_m is harmless only because the coefficient tuple is fixed.

## 4. Simultaneous initialization and source growth

This paragraph pays the seed instead of assuming a pre-existing simultaneous floor. Choose k1 from arbitrarily large one-angle Dirichlet returns so that A1>1 and2C0 delta1<1/8. For every a, u_(a,1,j)->0 as j->-infinity. For j->+infinity, (3.1) puts its distance from an integer within a term tending to zero plus1/8. All remaining finitely many factors are nonzero by integrality. Finiteness of B therefore gives

    gamma1 = inf_(a in B,j in Z)|cos(pi u_(a,1,j))| > 0.

Set D=10/log beta and K_m=ceil(2B_m+D L_m). Choose k2 sufficiently large from returns with ||k2 theta/pi||<=1/k2. Then delta2<=2pi delta1/k2 and L2->infinity. In particular log K2<=1.1L2 for all sufficiently large choices. Constants in this last assertion depend on the now fixed seed and coefficient tuple.

For m>=2 the source's exact choice still applies: with N=floor(exp(1.9L_m)), choose a return q<=N with ||q theta/pi||<=1/N, and take k=q if q>=K_m, otherwise k=ceil(K_m/q)q. The two cases yield

    K_m <= k_(m+1) <= exp(1.9 L_m),
    L_(m+1) >= 1.75 L_m,
    log K_(m+1) <= .75 L_(m+1),

and from m>=3, L_(m+1)>=2.1L_m. To check the constants: the large-q case gives L'>=2.9L-O(1)>=2.8L and B'<=2exp(1.9L)+O(1); the small-q case gives L'>=2.9L-log K-O(1)>=1.75L and B'<=3exp(1.1L)+O(1). The inequalities1.9<.75*2.8 and1.1<.75*1.75 give the next bound on K. Once log K<=.75L, the small-q lower bound improves to2.15L-O(1)>=2.1L. Fixed additive constants are absorbed by the initial lower threshold on L2, exactly as in the source.

For the simultaneous floor, the componentwise shift identity is

    u_(a,m+1,j)=u_(a,m,j+k)-u_(a,m,j-k).

At j<=0 the perturbation is at most C0 beta^(b_m-k) beta^j. At j>0 apply (3.1) at the new level and reflect into tau(a). Thus the common floor obeys

    gamma_(m+1) >= gamma_m
        - pi C0 beta^(b_m-k_(m+1)) -2pi C0 delta_(m+1).    (4.1)

The first step from m=1 has error tending to zero as k2->infinity while gamma1 is fixed. For m>=2, the real-tail error is at most exp(-10L_m); the neutral errors are summable since L_m>=1.75^(m-2)L2. Choose k2 once so that the sum of every decrement is less than gamma1/2, and so that every Taylor perturbation below is at most gamma1/(4pi). This is compatible with the growth thresholds. Fix this sequence. A common gamma=gamma1/2 now works for every a,m,j. No seed is held fixed while silently changing the same multiplier.

## 5. All scalar losses are already controlled

Write f(t)=-log|cos(pi t)| and

    S_(a,m)=sum_(j<=0) f(u_(a,m,j)),   S_m=max_(a in B) S_(a,m).

Every negative tail converges geometrically. With epsilon=.01 the source Taylor estimate is

    f(v+w) <= (1+epsilon)f(v)+C w^2

when the common floor and small-perturbation conditions hold. The constant is fixed by gamma and epsilon. Reflection (3.1) therefore gives

    f(u_(a,m,j)) <=1.01 f(u_(tau(a),m,-j))+C delta_m^2,
    sum_(j<=n) f(u_(a,m,j)) <=2.01 S_m+C n delta_m^2.       (5.1)

Using the shift, summing the squared geometric tail and then reflecting yields

    S_(m+1) <= 1.01*2.01 S_m+C(1+k_(m+1)delta_m^2)
             <=2.0301 S_m+C'.

Here k_(m+1)delta_m^2<=exp(-.1L_m). Since L grows at least as2.1^m, while S_m=O(2.0301^m),

    S_m=o(L_m).                                             (5.2)

The factor remains2.0301 rather than growing with |B| because we use the maximum over the finite tau-stable family. The final finite product of r Fourier factors only multiplies S_m by the fixed r. This is the source's same loss operation with finite constants, not new simultaneous Diophantine approximation.

## 6. Biased independent factors and common Fourier frequencies

For every p in [0,1] and real t,

    |p exp(it)+(1-p)exp(-it)|^2
        =cos^2(t)+(2p-1)^2 sin^2(t) >= cos^2(t).              (6.1)

This is exactly the operative comparison in Bisbas–Neunhäuserer section4. It does not require probabilities bounded away from0 or1. Infinite products follow by taking finite sign sums and using absolute convergence of the defining random series; the cosine lower product is positive by the established loss bounds.

At xi_(m,n)=pi d A_m beta^n, independence and (5.1) give, uniformly over ALL probability arrays,

    |E exp(i xi_(m,n)Y)|
        >= exp[-2.01 r S_m-C r n delta_m^2].                 (6.2)

Take J_m=floor(exp(L_m)). For0<=n<=J_m the right side is at least exp(-E_m), where E_m=2.01rS_m+C r J_m delta_m^2=o(L_m). This is stronger than needing an individual nonzero mean. The sequence, all constants, and the modulus bound are independent of the probabilities; only the argument of each expectation can vary.

The source phase-window proof would already give singularity after centering discarded biased tails. There is no need to stop there: the actual primary entropy proof uses these same modulus bounds and gives the stronger uniform dimension reduction below.

## 7. Norm separation and the rotated positive product

Let D0={sum_i a_i e_i:e_i in{+/-1}} be the finite digit set. Its distinct elements, not their representations, are the relevant alphabet. For a length-N block put X_N=sum_(n<N)beta^(-n)D_n, merging equal atoms. If x!=x' are atoms, d(x-x') is a nonzero algebraic integer. At tau its absolute value is at most C beta^N, and at each nonreal embedding at most C N, since D0 is fixed. Its nonzero integer norm implies

    |x-x'| >= c beta^(-N)N^(-2),                             (7.1)

with c>0 depending only on beta and the finite coefficient tuple. Zero differences have already been merged and are never norm-bounded. The same constants hold for all probability arrays, including zeros in the atom probabilities.

Let R=(sum_i|a_i|)/(1-beta^(-1)); |Y|<=R. Choose an integer q>=1 with Q=beta^q>2. At one sufficiently large m use n=0,q,2q,...<=J_m. These frequencies start above pi since d A_m>=1 and have ratio Q. Let M=1+floor(J_m/q), xi_M the largest, and

    N=J_m+ceil(log_beta(pi d A_m)).

Then beta^(-N)xi_M<=1. Since b_m<=K_m<=exp(.75L_m) eventually and log_beta A_m<=b_m, we have N=exp(L_m)(1+o(1)), M asymptotic to exp(L_m)/q, and log N=L_m+o(1).

Put a=min(1/2,exp(-E_m)). For each frequency choose a unit complex number omega_j with omega_j E exp(i xi_jY)=|E exp(i xi_jY)|. The positive product

    P(y)=product_(j=1)^M [1+a Re(omega_j exp(i xi_j y))]

has exactly the same integral and logarithmic Lipschitz bounds as Cheng–Fang–Ma–Zhang Lemma2.1. The rotations change coefficient phases, not magnitudes. The chord inequality gives E log P(Y)>=M Psi(a), with

    Psi(a)=((1+a)log(1+a)+(1-a)log(1-a))/2 >=a^2/2.

For completeness, every nonconstant expansion term whose largest index is j has frequency at least c_Q xi_j, c_Q=(Q-2)/(Q-1), and total absolute coefficient a(1+a)^(j-1). Thus its integral over any containing interval is bounded by the same geometric sum as the primary proof. Also Lip(log P)<=aQ xi_M/((1-a)(Q-1)). Since a<=1/2, the resulting integral and Lipschitz constants are uniform in m and in every rotation.

With eta_N=beta^(-N), let G=floor(Y/eta_N). Use the integral of P on each occupied cell, normalized by its integral on their union, as a comparison probability vector. The union lies in[-R-1,R+1]; positivity bounds its integral by the integral over this containing interval. The Lipschitz bound and nonnegative relative entropy then give

    H(G) <= N log beta - M Psi(a) + C1.

This does not apply an oscillatory interval bound to an arbitrary union. The remainder Y-X_N is bounded by R eta_N even for nonstationary arrays. Conditional on G, possible X_N lie in an interval of length(1+2R)eta_N. By(7.1) there are at most C2 N^2 distinct atoms. The entropy chain rule gives

    H(X_N) <= N log beta -(M a^2)/2 +2log N+C3.              (7.2)

All constants depend only on beta and the coefficient tuple. This proof did not require symmetry, stationarity, or identical distributions, only the Fourier lower bound and fixed finite support.

Since a>=exp(-o(L_m))/2, M a^2 grows as exp((1-o(1))L_m), while2log N+C3=O(L_m). Fix one finite m and its N so large that

    Delta := (M a^2)/2-2log N-C3 >0.

If desired replace Delta by min(Delta,N log beta/2) to keep a positive convenient slack. We obtain the **uniform finite-block bound**

    H(X_N) <= H_* := N log beta-Delta <N log beta            (7.3)

for every array, and therefore for every tail-shift of every array. No entropy rate, infinite-cylinder enumeration, or sample-dependent N is needed.

## 8. Nonstationary block cover, with its strong law paid

Group the signs into consecutive blocks of this fixed length N. Their merged values B_j are independent, but need not be identically distributed. They take values in a single finite set of size K_N<=2^(rN). Write p_j(b)=P(B_j=b). Each H(B_j)<=H_* by(7.3), applied to the corresponding tail probability array.

For the actually drawn atom define Z_j=-log p_j(B_j); zero-probability atoms never occur. Uniformly in j,

    E Z_j^2 = sum_(p_j(b)>0) p_j(b)(log p_j(b))^2
               <=4K_N/e^2 <infinity,

because max_(0<=p<=1) p(log p)^2=4/e^2. Thus Var(Z_j) is uniformly bounded, even when probabilities approach0 or1.

An elementary strong law now suffices. For independent centered T_j=Z_j-EZ_j with variance at most V, the maximal inequality

    P(max_(k<=n)|sum_(j<k)T_j| >=t) <= n V/t^2

follows by partitioning according to the first crossing k and using independence/zero mean of the remaining sum: E S_n^2 on each first-crossing event is at least E S_k^2 on that event. At n=2^l and t=epsilon2^l the probabilities are summable in l. The union bound on their tails shows only finitely many crossings almost surely. Comparing each integer n with its next dyadic endpoint, and then taking countably many epsilon->0, proves

    (1/m)sum_(j<m)(Z_j-EZ_j) ->0 almost surely.

Consequently almost every block sequence has prefix probability at least exp[-m(H_*+epsilon)] for all sufficiently large m. Since all length-m block probabilities sum to1, at most exp[m(H_*+epsilon)] prefixes meet this threshold. Each specifies a real interval of diameter2R beta^(-Nm), because the remaining digits have bounded support regardless of their probabilities.

The eventually-always union of these finite covers is Borel and has full probability. For t>(H_*+epsilon)/(N log beta), the sum of t-th powers of covering diameters tends to zero. Taking the countable union over starting times, and intersecting the full-measure Borel sets for a countable sequence epsilon->0, gives

    dim_H Law(Y) <= H_*/(N log beta)=1-Delta/(N log beta).

This proves the paid conclusion of section2, with eta=Delta/(N log beta)>0. It also explains why simply parking “nonstationary dimension” as an unpaid operation would be wrong: the finite-alphabet information variance bound supplies it classically.

## 9. Why all real coefficient sums are not a viable unrestricted extension

Take beta=beta1, the root of X^4-X^3-X^2-X+1 in(1,2), and let mu be its unbiased source measure. The source and the primary elementary classification give beta>5/3>sqrt(2), beta<2. The even-position subseries has contraction rho=beta^(-2)<1/2. Its two first-level intervals are disjoint, and the minimum gap between level-n intervals is a positive constant times rho^n. Each such interval has mass2^(-n).

If rho^n<=t<rho^(n-1), an interval of length2t meets only a bounded number of level-n cylinders, with bound depending on rho. Hence the even-digit law mu_even satisfies

    mu_even([x-t,x+t]) <= C t^s0,
    s0=log2/(2log beta)>1/2.

Since mu=mu_even * (beta^(-1)mu_even), convolution with the odd-digit law preserves this bound by integration. Thus rho2=mu x mu on R^2 has rho2(B(z,t))<=C't^(2s0). A dyadic shell sum proves I_1(rho2)=double-integral|z-z'|^(-1)d rho2(z)d rho2(z')<infinity.

Here is the classical projection step without treating an unread transitive reference as a proof. Let mu_theta be the projection of rho2 onto the unit direction e_theta. Smooth it by the uniform density on[-epsilon,epsilon]. Expanding its squared L2 norm yields

    ||mu_theta * phi_epsilon||_2^2
       <= (1/(2epsilon)) double-integral
             1_{|(z-z') dot e_theta|<=2epsilon}d rho2(z)d rho2(z').

For a nonzero vector v, the angular measure of {|v dot e_theta|<=2epsilon} is at most C min(1,epsilon/|v|). Therefore the angular integral of this L2 norm is bounded by C I_1(rho2), uniformly in epsilon. Fatou along epsilon->0 shows that for almost every theta a subsequence of the mollifications is bounded in L2. Weak compactness of L2 and convergence against compactly supported continuous test functions identify its weak limit as a density of mu_theta. It is an L2 density. This is the same finite-energy projection operation in Falconer–Mattila Theorem2.1(ii), of Kaufman/Marstrand type.

For cos theta!=0, a nonzero rescaling turns that projection into the law X+tX', t=tan theta, for independent X,X' with law mu. The change of variable between angle and slope preserves null sets locally. Hence

    mu * (t mu) has an L2 density for Lebesgue-almost every real t.

On the other hand, the paid arithmetic composition above makes it singular, indeed of dimension<1, for every t in Q(beta). There is no contradiction: that field is countable. An extension asserting singularity for every real t is false. The argument does not identify the complete exceptional slope set, settle a particular coefficient outside the field, or furnish any full new classification. None of those unspecified problems is offered as a parked nominee.

## 10. Operation comparison and outcome

The source already owns the small-conjugate products, the trace/shift/reflection identities, the cosine floor, the2.0301-versus2.1 loss margin, and the independent-block phase separation. The primary2610.12072v2 already owns the positive-product Fourier-to-Shannon estimate, containing-interval normalization, algebraic atom separation and finite-block dimension cover. Bisbas–Neunhäuserer already displays the nonstationary biased-factor inequality. Passing to a finite tau-stable coefficient family only alters fixed constants and uses the same single neutral angle. Rotating Fourier phases, finite-alphabet information variance, the elementary maximal inequality, and the projection-energy argument are classical compatible operations.

Thus the strong field-coefficient/nonstationary dimension conclusion is recorded as the **paid integrated reduction**, not as a substantial-contribution nomination. No new nonroutine operation beyond these was isolated. The failure of the all-real extension is an exact classical diagnostic, not evidence that the field conclusion is substantial and not a universal impossibility/exhaustion claim.

There is no unpaid mathematical bridge inside the stated composition being deliberately parked as a candidate. What remains absent for this discovery task is a distinct, fully specified, proof-feasible substantial result after the composition. The old sextic and full Markov questions retain their original obligations, and are neither weakened nor renamed. No theorem was frozen; no independent grades or campaign count are assigned. The parent alone integrates and reviews.
