# T096N126 — independent correctness review R1

**PASS, original frozen theorem without repairs**, conditional on the stipulated pinned OpenAI statements and operative proofs and the accepted R012/I38 project theorem. No mathematical blocker was found. This is a correctness decision only: no contribution rating, acceptance, count, or worldwide-priority claim is assigned. No current contribution review was inspected or used. The parent's preliminary impression was not used as evidence.

## Exact theorem reviewed

For standard Gaussian measure gamma_d and T_rho f(x)=E f(rho x+sqrt(1-rho²)Y), define

    S_rho(A)=sum_i [<1_Ai,T_rho 1_Ai>-gamma_d(A_i)²].

There exists ONE absolute rho_0 in (0,1), independent of dimension, number of labels, partition and cell masses, such that for EVERY finite d>=2, k>=3, EVERY measurable labeled partition A, allowing arbitrary masses and empty cells, and EVERY 0<rho<=rho_0, S_rho(A)<=S_rho(P). Equality holds exactly for orthogonal and label transforms of three origin-centered planar sectors of angle 2pi/3, extended by the full orthogonal factor, with all remaining labels empty, modulo Gaussian-null sets.

The reviewed scope has SHA256 `ec4ebab8030a197d780522b2b64d841b3a06de167a32945832361f190d92d382`; the proof has SHA256 `c60417b4efd8f2859436974e7e4c1d2eee1cad4d0c06022474fd9ecc6ec7ea59`. No local, fixed-mass, finite-label-bound, finite-dimension-bound, asymptotic, or subsequence substitute is used. The threshold remains existential. This review does not assert an effective numerical threshold or quantitative noise stability.

## 1. Actual inherited operational contract

The pinned source096 main theorem supplies F(A)=sum_i|z(A_i)|²<=B², B=3/(2sqrt(2pi)), for every finite measurable partition, not merely for extremizers. Its attaining-sector calculation gives z(P_i)=B t_i for a normalized equilateral score array t with three active labels, |t_i|=1/sqrt(3), |t_i-t_j|=1, and all other scores zero. The actual source main statement and extremizers file were inspected for scope; their truth is stipulated, not audited.

The crucial inherited input is stronger than R012's distance headline. In the ACTUAL I38 Sections 6.2–7, (6.10) gives e(v)>=c_V dist(v,T)² for norm-one score arrays with a single dimension- and label-independent c_V>0. Put v=Z_A/sqrt(F). The assigned-label comparison gives M(v)>=sqrt(F), so e(v)<=B-sqrt(F). Every t maximizing <t,Z_A> minimizes ||v-t||², because

    ||v-t||²=2-2<t,Z_A>/sqrt(F).

Thus every maximizing frame has the same minimizing distance and obeys (6.10). There is no restriction to one specially selected polar frame. The exact squared-pairing identity yields

    J_t=B-<t,Z_A>
       =B-sqrt(F)+(sqrt(F)/2)||v-t||²
       <=[B^(-1)+(2c_V)^(-1)](B²-F)=C_0 Delta.

The passage to the last bound uses B+sqrt(F)>=B and sqrt(F)<=B. The compact finite union of frame orbits attains the maximum for each finite d,k. No uniform bound on the number of orbits is required.

I38 (7.2) applies to each such frame: three active score differences have variance one; all inactive labels share the same zero score, so they require just one radial event. For mismatch probability epsilon, the margin bound Pr(margin<=s)<=9s gives J_t>=epsilon²/36 at s=epsilon/18. In particular epsilon<=6sqrt(J_t). The historical R2 calibration discussion confirms this exact contract; the historical R3 record is used only to identify the inherited result and its operational scope, not as a verdict on T096N126. Countable compactification, equality, extra-label activation and uniform score coercivity remain inherited. They are not reconstructed as new results here.

## 2. Weighted planar estimate: all sublevels and all tails

I checked Lemma 2.1 directly. Let W(t)=exp(t²/10), l(t)=|t|/(1+|t|). On |t|<=1 the sublevel l/W<=lambda implies |t|<=2exp(1/10)lambda; bounding W and the Gaussian density gives at most 4exp(1/5)lambda/sqrt(2pi). On |t|>1 the same sublevel implies lambda W>=l>=1/2, hence W<=2lambda W². The integral of W² is finite since its Gaussian integrand decays as exp(-3t²/10). Therefore (4) holds for every lambda>0. With support restricted to |t|>T>=1 its constant can be taken as

    K_T=2 E[exp(G²/5) 1_{|G|>T}] -> 0.

This restriction genuinely improves the constant; it does not merely bound the mass of the tail. Splitting an arbitrary 0<=h<=1 at the sublevel gives E(Wh)<=Klambda+E(lh)/lambda. Optimization, with the zero-integral limit treated separately, proves (5).

For nearest-full-line pieces, ties are resolved measurably and there are exactly three pieces independent of k,d. In normal/tangent coordinates (t,s), the elementary inequality

    1+sqrt(t²+s²) <= (1+|t|)(1+|s|)

proves v>=l(t)/(1+|s|). Applying the scalar estimate on each fiber and Cauchy–Schwarz with factors sqrt((1+|s|)exp(s²/5)) and sqrt(b(s)/(1+|s|)) gives (7). The extra tangent moment D=E[(1+|G|)exp(G²/5)] is finite. The piece indicators stay inside h; no rectangular-support assumption is introduced.

For a function supported on |u|>R, divide each piece disjointly into |t|>R/sqrt(2) and its complement. On the complement |s|>R/sqrt(2). Write D_T=E[(1+|G|)exp(G²/5)1_{|G|>T}]. One valid full planar tail constant is

    C_tail(R)=24 max(K_{R/sqrt(2)} D, K D_{R/sqrt(2)}), R>=sqrt(2).

Indeed there are six pieces and each has squared-integral bound at most 4 times the displayed maximum times its own weighted integral. Both terms tend to zero. This explicitly verifies the normal-tail and tangent-tail branches, including mass arbitrarily close to the extended boundary lines. Those full lines are only a lower weight; they need not be actual cell interfaces everywhere.

## 3. Mehler, arbitrary orthogonal dependence, and all degrees

The normalized Gaussian Hermites are an orthonormal basis. Their OU eigenvalues follow, for example, by applying Gaussian expectation to exp(tx-t²/2): the resulting generating function is exp(rho tx-rho²t²/2). Tensor products give total degree in any finite dimension. Thus no regularity of indicators is required for the L2 spectral identities.

In two dimensions the OU density kernel relative to gamma_2 is

    K_q(u,z)=(1-q²)^(-1)
       exp((2q u·z-q²(|u|²+|z|²))/(2(1-q²))).

Setting z=u gives the stated diagonal. Its Hermite feature norm at q=1/4 is (1-q²)^(-1/2)exp(|u|²/10), exactly the weight above. The Hilbert-space triangle inequality, first for finite feature vectors and then by monotone convergence, proves (8) even for signed f. The relevant weighted integral is finite for |f|<=1. There is no pointwise sign assumption on f.

On each y-fiber this bounds sum_alpha q^|alpha||f_alpha(y)|². Integrating over y and using Parseval there gives precisely sum_{alpha,beta}q^|alpha||c_{alpha,beta}|². No independence of f, of its mismatch set, or of its labels from y is used. For total degree at least two, the multiplier comparison in the proof is valid in all three cases: planar degree >=2, planar degree 1 with orthogonal degree >=1, and planar degree 0 with orthogonal degree >=2. In the latter two cases the right side is respectively rho²/q and rho²/q², both large enough. Thus arbitrarily many purely orthogonal Hermite modes are included.

For total degree one, 1<=q^(-1)q^|alpha| for both possibilities (planar degree 1 or 0). Consequently a legitimate tail first-chaos coefficient is

    e(R)=q^(-1)(1-q²)^(-1) C_tail(R) -> 0.

It controls ALL coordinates of z(f). Summing the scalar bounds over finite labels gives the array estimates without a label factor: the weighted integrals also sum. This is the uniform tail estimate needed later, not a full-radius estimate deteriorating with ambient dimension.

On a mismatch, exactly two indicator differences have absolute value one. For a wrong active label, its gap is the nonnegative distance to its pair's full line and hence >=w; for an inactive label, the winning score is >=|u|/(2sqrt(3)). Since v<=w and w<=|u|, C_v=4sqrt(3) is a valid common constant in (10), on every measurable restriction. There is no missed factor two.

## 4. Exact cone comparison and gap-proportional local error

For each active pair the orthonormal coordinates in (13) describe their two entire sectors, not just neighborhoods of the shared ray. Integrating the b-coordinate of N(rho u,(1-rho²)I_2) over b'>=-x/sqrt(3), then reflecting x for the other sector, gives exactly (13). With mu=rho s>=0 the difference of the two normal densities is nonnegative. On x>=mu, the condition b>=-s/sqrt(3) gives rho b+x/sqrt(3)>=0, so the CDF is >=1/2. Direct integration gives

    integral_mu^infinity [phi_sigma(x-mu)-phi_sigma(x+mu)] dx
       =Phi(2mu/sigma)-1/2.

Thus the coefficient and sign in (14) are correct. A constant times min(mu,1) works uniformly for sigma in [sqrt(15)/4,1]. For example phi(2) is a valid constant after the factor 1/2, by the density lower bound when mu<=1 and monotonicity when mu>=1. The inequality min(rho s,1)>=rho s/(1+|u|) follows separately in those two regimes.

An inactive score is zero after centering, while the three active centered scores sum to zero. Therefore q_i=(1/3)sum_{j active,j!=i}(q_i-q_j). Both active differences are nonnegative in P_i and obey the previous estimate. This proves an absolute lower bound even when the assigned wrong label is newly activated. Choosing kappa to absorb the two mismatch indicators gives exactly D_T>=kappa rho V.

For the bounded-ball Taylor estimate, differentiation acts on the smooth Gaussian density integrated over a fixed cone. On the compact parameter set |rho|<=1/4, |u|<=R, mixed derivatives through two rho derivatives and one u derivative are dominated by an integrable Gaussian times a polynomial, with constants depending only on R. Taylor expansion of the u-gradient leaves an O_R(rho²) remainder. For active pairs, reflection makes the difference of remainders vanish on the FULL equality line. Integrating the normal derivative along the segment from (0,b) to (s,b), which lies within the same ball, multiplies the error by s=s_ij. This is why the estimate remains proportional to the gap arbitrarily close to an interface; a bare uniform O_R(rho²) bound would not suffice.

For an inactive comparison the remainder vanishes at the origin for every rho, by the isotropic angular mass 1/3. Integrating its gradient radially gives O_R(rho²)|u|, and the winning active score is >=|u|/(2sqrt(3)). This proves (12) there too. Integrating over the actual assignment proves all three statements of (15).

## 5. Truncated partitions and the cost of moving the frame

A^N is exactly A on the planar ball times the full orthogonal factor and exactly P outside. Each indicator remains zero or one, all labels sum to one, and it is a legitimate measurable partition. Hence both the stipulated first-moment bound and the inherited calibration apply to it, regardless of masses or empty labels.

With G=z(g), H=z(h), a=||G||, b=||H||, the identity <t,G>=-J_N gives

    Delta(A^N)=2B J_N-a²,

so a²<=2B J_N. No tail score loss has been included in this identity.

Here is an explicit constant check of Lemma 4.1. Take, for instance, delta_*=B/(8sqrt(3)). Nearest-frame minimality and the triangle inequality give B||t_N-t||<=2delta_*. Different three-label supports are separated by at least 1/sqrt(3); thus the support cannot change. This estimate is uniform even as k grows, and includes possible label permutations and reflections within the common support.

Write t=QE, t_N=Q_NE, EE*=I_2/2. Then ||E||_op=1/sqrt(2). For M=Z_A^head E*,

    sigma_min(M)>=B/2-delta_*/sqrt(2)>B/4.

The maximizing Q is the unique polar factor of this full-column-rank matrix on the selected support. This follows from the SVD trace maximization over d-by-2 isometries; arbitrary ambient codimension causes no extra term. For every isometry Q', I-sym(Q'^*Q) is positive semidefinite and has trace ||Q-Q'||_F²/2. Therefore the coefficient B/8 in (18) is correct even if Q'^*Q is not symmetric.

Optimality of Q_N for the truncated centroids gives

    (B/8)||Q-Q_N||_F² <= ||Q-Q_N||_F b/sqrt(2).

Cancellation when the difference is nonzero, with the zero case immediate, yields ||t-t_N||<=4b/B. The original total-centroid optimality of t now bounds the regret difference by

    0<=J_t(A^N)-J_tN(A^N)<=4b²/B.

This is the essential paid frame change; it does not assume t remains optimal after truncation. Since ||Z_A^N||>=B-delta_*>0, the calibration applies at t_N and gives (17) with

    c_*=1/C_0,    C_*=4/(B C_0).

These explicit choices explain the constants already allowed in the original proof; they are not a replacement lemma or repair. The positive singular-value bound and support separation come from total and truncated centroid closeness, not from an unproved regularity property of A.

## 6. Entry, exact centered expansion, and absorption

The centered energy is exactly sum_{m>=1}rho^m sum_i||Pi_m 1_Ai||². Its entire indicator norm budget is sum_i gamma(A_i)=1. Thus any contender S_rho(A)>=S_rho(P) satisfies rho B²<=rho F(A)+rho² and 0<=Delta(A)<=rho. This is valid without existence of a noise optimizer. By itself it gives only neighborhood entry, which the proof correctly recognizes.

At rho<B²/2 the first moment is positive. Selecting a maximizing t and using the inherited calibration gives epsilon<=6sqrt(C_0 rho). Orthogonal projection to first chaos is a contraction on the summed array Hilbert space, giving both squared centroid distances in (21) at most 2epsilon, also for the truncated partition since its mismatch set is a subset. For example rho<=delta_*^4/(144 C_0) suffices for both distances to be <=delta_*. This entry threshold is independent of R, so it creates no circular choice of constants.

For f=1_A-1_P, expand with the self-adjoint operator T_rho-Pi_0, rather than T_rho alone. Its linear term is -2(D_N+D_T), including the constant active mass subtraction 1/3; its quadratic term is rho||G+H||²+Q, with Q>=0 containing all degrees >=2. Hence (22) has no missing cell-mass term. Lemma 2.1 applied to f, not a fictitious independent pair g,h, gives Q<=C rho²(U+V). It already covers every cross term between the two regions. Applying its tail bound separately to h gives b²<=e(R)V.

Substituting D_N>=rho B J_N-C_R rho²J_N and the exact deficit identity gives

    -2rho B J_N+rho a²=-rho Delta(A^N).

Then (17) produces precisely

    -c_*rho J_N+(C_*+1)rho b²+2rho ab
       -2kappa rho V+C'_R rho²J_N+C rho²V.

Every coefficient in (24) is accounted for: the +1 multiplies the direct b² term and the +C_* is the calibration cost. Young's inequality with eta=c_*/(8B) gives 2ab<=c_*J_N/4+(8B/c_*)b². Thus C_b=C_*+1+8B/c_* is independent of R,rho,d,k,A.

First choose one R>=sqrt(2) so that C_b e(R)<=kappa/2. Only then choose rho_0 positive, below the entry and spectral thresholds, with C'_R rho_0<=c_*/4 and C rho_0<=kappa/2. For inclusive endpoint safety one may take rho_0<=B²/4 as well. Finite positive constants and e(R)->0 ensure these choices exist. The remaining coefficients are exactly

    S_rho(A)-S_rho(P)<=-(c_*/2)rho J_N-kappa rho V.

This is uniform for the entire interval 0<rho<=rho_0, with no exchange of dimension, labels or rho limits.

## 7. Equality, dependencies, and retained objections

A contender forces J_N=V=0. The original winning score is strictly larger than each incorrect score off finitely many tie hyperplanes; a zero score can win only at planar radius zero. Hence J_N=0 eliminates every mismatch inside the ball almost everywhere. The weight v is positive off three full planar lines, whose cylinders have Gaussian measure zero in every finite d, so V=0 eliminates every mismatch outside. Therefore the contender itself is the selected propeller, including empty inactive labels. Orthogonal and label invariance gives the converse equality. A putative strict improvement would be a contender and thus have exactly the propeller value, a contradiction. This establishes both the inequality for all partitions and the full stated equality class.

No additional primary noise theorem is a premise in Sections 2–5. The classical Gaussian identities and linear algebra needed there have been justified above. The source096 kernel application actually defines its objective using projection onto degree ONE, and the Unique Games companion supplies that first-moment kernel consequence; neither is imported as a whole-noise theorem. HJN equality is inside the accepted I38 inheritance and is not freshly truth-audited or rerun here.

The prior diagnostic remains valid: exact smoothed cone scores saturate far along an interior ray, whereas the linear score grows. A global Taylor remainder bounded by C rho² times the untruncated linear score gap is unavailable by that method. The present proof pays the tails using exact smoothed loss and a vanishing tail centroid coefficient. It also explicitly pays frame reselection. Fixed-mass dimension reduction to m-1 does not eliminate arbitrary extra labels. Separate scalar rearrangements need not form a partition. Heilman's stronger unrestricted THREE-label derivative theorem, already disclosed by the author, must not be reduced in comparison to an equal-mass introduction alone. None of those comparisons is needed for this correctness verdict or treated as a proof of the all-label transfer.

The preserved chronology is: the initial feasibility note ended with an unpaid linear tail term; the later weighted-tail, cone and polar calculations occurred BEFORE freeze and are disclosed in the prefreeze addendum; the complete proof was written afterward. The frozen bytes agree with their supplied anchors. No integrity result or numerical experiment is a mathematical gate, and no numerical experiment was needed for this review.

**Required repairs: none. Original full target: PASS.** Exact reading and provenance limits are in `reading-provenance.md`; reproduction and rights boundaries are in `README.md`. These explanatory constant calculations do not alter the author proof or theorem.
