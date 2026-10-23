# Arithmetic162i: quantitative reconstruction and the uniform whole-law interface

PREFREEZE / no nominee. This is a feasibility record, not a frozen statement, author-proof submission, correctness verdict, contribution grade, acceptance or count decision. Source073 and all its operative upstream proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. The entire completed Arithmetic162h theorem and integrated technical reduction are closed input; none of that theorem is retried here. All older obligations and dispositions supplied in the assignment remain unchanged.

The developed direction is quantitative regularity of unpinned distance laws, followed by a test of whether it can be made uniform for the entire original measure. The fixed retained-measure regularity closes by source operations and elementary Fourier estimates. No distinct nonroutine closed bridge to the full uniform target was obtained. The record below carries the strongest available reduction, including a quantitative tail in the actual coarse-filter proof that is absent from the abstract monotone-shell hypothesis. It does not nominate that routine consequence or merely call its remaining gap a result.

## 1. Operative input, with quantifiers retained

Write S=d/2. The actual source theorem assumes an integer d>=2, compact E in R^d, and dim_H E>S. A Frostman probability with exponent s>S can be chosen, with s strictly below dim_H E. Finite t-energy is used at t<s, never at an unearned endpoint. No Ahlfors lower bound, packing equality, Fourier decay or product assumption on E is inserted.

The source first restricts and normalizes to separated compact pieces with fixed positive separation, a common exponent S+chi, and a small original cross-direction patch. These are allowed operations in the paid source theorem. They are NOT a substitute for retaining an entire original measure in the later uniformity question. Auxiliary projections preserve finite energy almost surely, and bounded-potential restrictions give simultaneous projected Frostman bounds. In odd d=2k-1, the source treats positive mass on a k-plane by its classical distance argument; otherwise its projection to R^(k+1) has no hyperplane mass. A further projection to R^(floor(S)+1), radial L^p bounds, density truncation, and lifting pay the integer angular exponent. The linear-gain/contact-interval bootstrap pays the remaining half dimension in odd d.

At frequency R=2^N, its actual output is

  alpha_N = D_#(W 1_Gamma_N (mu_1 x mu_2)),
  tau_N   = D_#(W 1_Gamma_N Theta_N (mu_1 x mu_2)),
  D(x,y)=|x-y|, W=D^(-(d-1)/2), 0<=Theta_N<=1.

The cross distances lie in one compact interval [d0,d1] inside (0,infinity). The source proves, for fixed data and parameters,

  alpha_N decreases to alpha != 0,
  ||alpha_N-tau_N||_TV <= C 2^(-eta N),
  integral_(2^(N-1)<=|r|<=2^(N+1)) |tauhat_N(r)|^2 dr <= C 2^(-gamma N),       (1)

where eta,gamma>0. Constants and thresholds are not automatically uniform when starting measures, restrictions or requested mass loss vary. The masks need not be nested. Gamma_N is constant in even d; in odd d it is a decreasing union-of-products coarse filter, with at most C2^(2d omega N) product atoms.

The shell estimate genuinely uses arbitrary bounded spatial endpoint multipliers, but not an arbitrary bounded multiplier of the pair (x,y) at unit cost. Product atoms cost up to their number in the Fourier L2 norm, hence 4d omega in the squared shell exponent. Differentiation is angular, preserves every test support, and has a fixed budget selected before N grows. No spatial derivative of a Borel indicator is taken.

The shell entry exponent is precisely

  min_j k_j(0,c) - (V_1([c,N])+V_2([c,N]))/2
       + C_d(kappa+sigma/kappa) + 4d omega + o(1).

Here c is the last depth where either excess profile is <=beta. Both potentials are >=2beta-O(1/N), while min k_j<=beta+C_d sigma. Choosing beta, then kappa, sigma, omega gives a negative exponent. Changing to a pin diagonal or a jointly varying metric would change an actual interface, not just the notation. The two independent angular variables, four independent endpoints, both graph degrees, and the original Euclidean phase are retained throughout this record.

## 2. Strongest primary and original-history comparison

The primary operations actually read before this derivation are: Orponen, arXiv:1710.11053v3, the complete radial Lp proof and its theorem interfaces; Orponen-Shmerkin-Wang, arXiv:2209.00348v1, complete Section 2, including the thin-tube definition, planar Furstenberg interface, full two-case bootstrap and iteration; Ren, arXiv:2309.04097v1, complete Section 7 and the plate-parameter companion subsection; Shmerkin, published JEMS 25 (2023), complete Appendix B, printed pp.4200--4203, with formulas recovered visually from the actual PDF. Exact extents and unread material are in private/READING-ISOLATION.md. The recursive Orponen-Shmerkin discretized Furstenberg proof was not independently read; its input is already part of the stipulated canonical operative proof, not a new strengthened premise.

Shmerkin's Appendix B already handles prescribed arbitrarily small loss of pin and source mass, conditional on a quantitative nonconcentration scale. Its last proof uses positive increments P_n(x) outside previously deleted plates, not an unjustified sum of full plate masses. Ren's refinement pays a relative-scale power and compares new losses against earlier plates. These are stronger than merely saying there are few heavy plates. The source builds its own dyadic-cell product filters and a late-new-loss estimate from that mechanism. Consequently neither arbitrary-small-mass deletion nor relative plate scales alone can be claimed as an additional operation.

The actual original i124 §§2--6 and i130 §1 were read. They already develop the fibrewise monotone reconstruction, identify the diagonal pin variance, track the inverse-cell-mass loss in random-sign localization, and give actual irregular Frostman examples. Those mechanisms are not proposed again. In particular an L2 bound uniform over bounded endpoint multipliers does not bound the pin-diagonal L2 norm: the partition approximation requires factors 1/nu(Q). The earlier conditional derivative/sign route needs a shell exponent gamma>3, which the present small source gamma does not supply. No restriction of that target, new grade, or renamed pinned claim is offered.

## 3. Recover the quantitative tail actually present in the fixed coarse filter

This calculation is an applicability deduction from the complete source proof, not an audit of it.

In odd d=2k-1 let s in (k-1/2,k) be the auxiliary Frostman exponent and put a=s-(k-1)>1/2. In the source coarse-filter proof, b>0 is chosen sufficiently small and C0 is its heavy-net constant. Let E_j be the pair deletion at width 2^(-j), with starting scale j0. Its estimate for NEW deletion mass, for j>4j0, is

  (rho_1 x rho_2)(E_j minus union_(j0<=i<j) E_i)
       <= C 2^(-j(a/2-2C0 b)) + 2^(-b floor(j/3)).                      (2)

Both exponents are positive by its parameter choices. Set

  v = min(a/2-2C0 b, b/3)>0,    J_N=floor(omega N).

For J_N>4j0, every pair in Gamma_N minus Gamma_infinity belongs to its first deletion E_j for some j>J_N. These first-deletion pieces are disjoint. Summing (2) gives

  (rho_1 x rho_2)(Gamma_N minus Gamma_infinity) <= C' 2^(-v J_N).

Pullback through the chosen projections preserves these product masses. Since W is bounded on the fixed separated cross product, positivity implies the exact equality between the TV of the pushforward difference and its weighted mass. Therefore

  ||alpha_N-alpha||_TV <= C'' 2^(-delta N),    delta=omega v>0,           (3)

once N is larger than a data-dependent threshold. One can decrease delta if desired to absorb harmless roundings. This uses the late-loss PROOF, not merely the stated preparation proposition. It does not assert a rate in the abstract monotone-shell lemma, which is correctly formulated without one. It also does not give a uniform threshold j0 over all non-plane-charging Frostman measures.

In even dimensions Gamma_N is the entire prepared product, so the left side of (3) is identically zero. In the exceptional exact-plane branch the source already supplies an L2 distance measure by the classical threshold. That branch has a different chosen measure; it is not a bound for all cross terms of the original measure.

## 4. Full scalar quantitative deduction for the retained measure

Fix smooth Fourier cutoffs Q_N with multiplier theta(2^(-N)r), theta=1 on [-1,1], supported in [-2,2], and let P_N=Q_N-Q_(N-1). All kernels are fixed rescalings of Schwartz functions. This fixes the approximate-identity requirement; the earlier arbitrary-Q failure is not repeated.

The measures in (1) have uniformly bounded masses and are supported in [d0,d1]. On any fixed larger interval J, Cauchy--Schwarz and Plancherel give

  ||P_N tau_N||_(L1(J)) <= C_J 2^(-gamma N/2).

Outside J, the distance to the support is bounded below. Integrating the Schwartz tail of the band kernel gives

  ||P_N tau_N||_(L1(R minus J)) <= C_L 2^(-L N)

for any prescribed L>0. This step is needed: a global L1 bound does not follow from a global L2 bound alone. Together with the bounded measure-to-L1 convolution norm and (1),(3),

  ||P_N alpha||_1 <= C(2^(-gamma N/2)+2^(-eta N)+2^(-delta N)).           (4)

In even d omit the last term. Choose any

  0<q<min(1,gamma/2,eta,delta)

in odd d, and omit delta in even d. Then ||P_N alpha||_1<=C_q2^(-qN). The finitely many initial bands and Q_(K-1)alpha have fixed finite norms. Thus their Fourier series converges absolutely in L1 to a density f of alpha, with

  sup_(N>=0) 2^(qN)||P_N f||_1<infinity.

This is the inhomogeneous B^q_(1,infinity) bound, with our fixed cutoff convention. To make its consequences self-contained, choose another smooth multiplier equal to one on the band support. Its convolution kernel has derivative L1 norm O(2^N). For g_N=P_N f,

  ||g_N(.+h)-g_N||_1 <= C min(1,2^N|h|)||g_N||_1.

Split the sum at 2^N|h|=1. The two geometric series yield

  ||f(.+h)-f||_1 <= C_q |h|^q,           0<|h|<=1.                     (5)

Similarly, the enlarged-band kernel has Lp norm O(2^(N(1-1/p))). Young's convolution inequality gives

  ||g_N||_p <= C_p 2^(N(1-1/p))||g_N||_1.

Consequently f belongs to Lp for every 1<=p<1/(1-q), by summing the bands; the low-frequency term is also in Lp. This does not claim the critical p endpoint, L2 when q<=1/2, pointwise Fourier decay, continuity of f, or an interval in its support.

The unweighted retained distance measure equals t^((d-1)/2) alpha. On [d0,d1] this factor extends to a bounded smooth function of compact support. Its translation increment is O(|h|), so (5) and the Lp conclusion persist. For its positive mass m, Hölder gives the usual lower bound |support| >= (m/||f_unweighted||_p)^(p/(p-1)). Constants depend on the entire fixed preparation, including normalization, separation and onset scales. No universal lower length for arbitrary E is asserted.

Everything in this section is a standard frequency-band calculation after the actually paid source construction. It is recorded to prevent treating these stronger fixed-data consequences as a new substantial result. No acceptance grade is assigned.

## 5. A sharp warning about upgrading the scalar interface to L2

The following concrete diagnostic does not model a Falconer set and is not offered as a counterexample to any distance theorem. It shows why (1) by itself, even with constant alpha_N and a power TV error, cannot silently produce L2 regularity.

Take 0<a<1/2 and 0<c<1. Choose pairwise disjoint intervals of lengths epsilon_j=2^(-j-4) accumulating at zero inside [0,1], and let phi be a nonnegative smooth bump supported in (0,1) with integral one. If x_j is the left endpoint of the jth interval, put

  f_j(t)=m_j epsilon_j^(-1) phi((t-x_j)/epsilon_j),   m_j=C_a2^(-aj),
  f=sum_(j>=1) f_j,   integral f=1,
  alpha_N=f dt for every N,
  tau_N=(sum_(j<=floor(cN)) f_j)dt.

For small N an empty sum is harmless. The positive omitted mass is O(2^(-acN)). At |r| comparable to R=2^N, for every integer M,

  |tauhat_N(r)| <= C_M sum_(j<=cN) 2^(-aj)(R epsilon_j)^(-M)
               <= C'_M R^(-M(1-c)-ac)

when M>a. Its shell L2 square is bounded by

  C_M R^(1-2M(1-c)-2ac).

Taking M large makes this O(R^(-gamma)) for any FIXED gamma>0. The constants depend on M. Thus all the scalar hypotheses hold, including positivity, fixed compact support, monotonicity equality and a power TV error. But disjointness gives

  integral f^p = C_(a,p,phi) sum_j 2^(j(p(1-a)-1)),

which diverges for p>=1/(1-a), in particular for p=2. A faster shell estimate for tau_N cannot repair the concentration hidden in its TV-small discarded mass. This explicitly defeats the proposed shortcut from shell smoothness to an unrestricted L2 conclusion. It does not show that source geometric restrictions permit these spikes.

## 6. The developed stronger direction, and a precise sufficient bridge

The full direction tested was the following UNFROZEN feasibility target, not an asserted theorem:

For each integer d>=2 and s in (d/2,d), do there exist p(d,s)>1 and a finite C(d,s,K), such that EVERY probability mu supported in the closed unit ball of R^d with mu(B(x,r))<=K r^s for every x and 0<r<=1 has its ENTIRE law

  nu_mu = [(x,y)->|x-y|]_#(mu x mu)

in Lp(R), with norm at most C(d,s,K)? No favorable support restriction, plane-exclusion hypothesis, packing equality, lower mass bound or selected pair filter is part of this target. There is no endpoint s=d/2 assertion. It is not the older pinned target.

The fixed-filter consequence above does not prove this target: nu_mu includes all discarded pair mass and all cross terms between any pieces. Countable positive restrictions with separate constants do not supply a uniform Lp norm. The following calculation identifies what quantitative retention would suffice, without declaring it available.

On a fixed separated product, let lambda be its full product measure and nu its distance pushforward (a fixed smooth positive weight can be included). Suppose that for every 0<epsilon<=1/2 there is a positive submeasure nu_epsilon<=nu such that

  ||nu-nu_epsilon||_TV <= C epsilon,
  ||P_N nu_epsilon||_1 <= C epsilon^(-A)2^(-qN)   for every N>=0,         (6)

with fixed q>0,A>=0,C, independent of epsilon,N and of the measures in the desired uniform family. This is stronger than allowing an untracked starting scale depending on epsilon. Then

  ||P_N nu||_1 <= C'(epsilon+epsilon^(-A)2^(-qN)).

Choosing epsilon=2^(-qN/(A+1)) proves a B^(q/(A+1))_(1,infinity) bound (or any smaller exponent below one), hence Lp for 1-1/p<q/(A+1). No nesting or common filter across epsilon is needed in this deduction, because nu itself is fixed. The missing work lies in (6), not in a further limiting theorem.

For the original self-product, nearby pairs can be bounded directly:

  (mu x mu){|x-y|<=r} <= K r^s.                                         (7)

The remaining pairs admit a finite separated cube decomposition at scale comparable to r. But normalization costs inverse masses, the number of cubes grows, and all constants in (6) must be controlled polynomially in r^(-1) and in retained masses before r can depend on N. Stating only (7) or applying the source separately to countably many separated pieces does not complete the desired estimate.

The primary radial argument does pay some of the requested quantitative dependence. For projected finite energies, Markov truncation at potential M removes O(I/M) mass; the resulting ball constant is O(M). In the radial Lp step an integrated density bound L permits removing pairs at angular density threshold T with cost <=LT^(1-p). Uniform good-pin restrictions follow by another Markov inequality. These costs can be explicitly balanced with epsilon. The actual source does not require cap exponents above the dimensions of those radial supports. Thus radial density truncation itself is not an unnamed hard bridge.

The problem is not solved by retaining only these comparatively easy losses. Odd-dimensional coarse preparation still uses the quantitative no-hyperplane-concentration scale to begin a small-total-loss filter. Shmerkin's full B.1 and Ren's full relative-scale variant retain this dependence. The next two calculations test rather than assume its uniform replacement.

## 7. Uniform failure of the qualitative plane-vanishing shortcut

In the auxiliary R^(k+1), k>=2, choose any s in (k-1/2,k). Let rho_h be normalized Lebesgue measure on a fixed k-dimensional cube times normalized Lebesgue measure on [-h,h], for 0<h<1, followed by one fixed rescaling into a bounded ball. The same argument works with two separated k-cubes, so separation does not cure this issue.

For r>=h, rho_h(B(z,r))<=C_k r^k. For r<h, it is at most C_k r^(k+1)/h<=C_k r^k. Since r^k<=r^s for r<=1, this family has a UNIFORM s-Frostman bound. Every rho_h gives zero mass to every affine hyperplane. Nevertheless, if H is its central k-plane, rho_h(H_h)=1. Therefore

  sup_(h>0) sup_H rho_h(H_r)=1 for every r>0.

There is no uniform modulus for the source's limit sup_H rho(H_r)->0 on this class, although it holds for each individual member. In the coarse-filter proof a j0 making initial loss small must consequently depend on h for this family. For coarse widths exceeding h, the heavy central plate captures all of both separated supports. Starting its deletion too early loses the whole cross product.

This is an actual family satisfying the hypotheses used at that interface. It disproves the UNIFORMIZATION OF THAT CHOICE, not the target in Section 6. The limiting plane has a stronger classical distance estimate. A correct proof might use a quantitative alternative that keeps, rather than deletes, concentrated plane pieces. That alternative has to be carried through original distances and all cross terms; it is not licensed merely by the fact that exact-plane support was an allowed source alternative.

## 8. Strongest attempted repair: use the classical estimate before the transverse scale

Here is an explicit compatible part of that alternative. Let two probabilities in R^(k+1) have a common s-Frostman constant, s>(k+1)/2, supports separated by a fixed a0>0, and lie within distance h of one affine k-plane H. Suppose their projected supports are still separated, as follows for h<a0/10. Write x=(u,z), y=(v,w) in orthogonal coordinates, with |z|,|w|<=h. Then

  0<=|x-y|-|u-v|
    = |z-w|^2/(sqrt(|u-v|^2+|z-w|^2)+|u-v|)
    <= C_(a0)h^2.                                                       (8)

On a Fourier shell |r|~R the phase difference is O(Rh^2). The stationary weight D^(-(k-1)/2) has the same O(h^2) comparison to |u-v|^(-(k-1)/2), with constants depending on a0. Hence the squared shell L2 error between the two weighted distance transforms is at most

  C_(a0) R^3 h^4.                                                        (9)

Using exponent (k-1)/2 here is intentional: this is the classical k-dimensional branch, not a covert change of S in the ambient recursive proof. The two weights are smooth positive functions of distance on separated supports; scalar multiplication can be handled only after obtaining the corresponding estimate.

For radii r>=h, a projected r-ball lifts into a fixed enlargement of a physical r-ball (one transverse coordinate of size h). Thus the projected laws have an s-ball bound at all r>=h, with a fixed constant. This need not hold below h. For R<=c/h, it is exactly the range needed in the frequency-R classical estimate:

  integral_(S^(k-1)) |rhohat_1(Rw)|^2 dw <= C R^(-(k-1)/2),
  average_(r~R) integral_(S^(k-1)) |rhohat_2(rw)|^2 dw <= C R^(-s).

The first inequality follows from the sphere kernel bound and annular summation of (1+R|u-u'|)^(-(k-1)/2). The innermost R^(-1)-ball costs O(R^(-s)); farther shells sum because s>(k-1)/2. The second follows from the Gaussian Fourier-ball majorant, using the ball bound only at radii >=R^(-1). Thus no energy below the known scale is silently required. The separated stationary-phase conversion from the source classical proof gives

  integral_(r~R) |tauhat_projected(r)|^2 dr
       <= C(R^((k+1)/2-s)+R^(-1)).                                      (10)

Equations (9)--(10) give the same decaying estimate in the original space when 1<=R<=c/h, since R^3h^4<=C R^(-1) there. This pays a real part of the proposed alternative with the correct Euclidean distance, finite-scale mass hypotheses, separation constants and weight. The source's auxiliary projection, by itself, would not have paid (8)--(9).

It still leaves a scale range. The source coarse filter with J_N=omega N can start past the transverse thickness only once R^(-omega) is much smaller than h, or R much larger than h^(-1/omega). The classical comparison just proved covers R up to order h^(-1); its pointwise phase-error bound cannot cover the entire intervening range. Even if (10) had arbitrary saving, (9) grows at fixed h as R tends to infinity. For a desired decay R^(-g), that comparison needs h<=C R^(-(3+g)/4). Shrinking the source's already small omega does not bridge this range.

An adaptive multiscale treatment might carry plane concentration as a state and use its intrinsic decay without flattening all later phases. To close (6) it would have to: preserve the full pair mass up to epsilon; control interactions between differently oriented or differently located plane pieces; bound the product-partition/symbol cost; retain the ambient profile and mask-support contracts on every transition; and provide one polynomial dependence on epsilon and geometric constants. No such transition estimate is proved here. These are specific compatibility obligations, not a claim that every proof must have this form or that the target is impossible.

## 9. Why no theorem was frozen

The retained-law Besov/Lp deduction is complete but is an elementary consequence of actual paid operations. The scalar spike construction invalidates an overstrong L2 shortcut. The thin-slab family invalidates the uniform qualitative plane-vanishing shortcut. The finite-scale classical comparison supplies a genuine compatible repair below the transverse scale, rather than stopping at that failed shortcut. It does not close the intermediate-scale and whole-mass estimate (6).

No fully viable distinct nonroutine theorem emerged, so no statement was frozen and no author-proof document was started. In particular this record does not turn the fixed-filter result, an easier no-plane subclass, a stronger dimensional hypothesis, or a conditional version of (6) into a nominee. The full feasibility target in Section 6 is left unchanged and unproved. The prior pinned, variable-metric, endpoint and common-vertex targets remain unpaid, not refuted. There is no exhaustive search, worldwide-priority claim, or worldwide-impossibility inference.
