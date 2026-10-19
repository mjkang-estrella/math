# Centered Gaussian noise stability: preselection, not a candidate

No theorem was frozen. All calculations here are feasibility work, made after reading the actual historical propeller proof and the primary interfaces specified below. The whole question considered was whether one absolute rho_0>0 makes the three-sector propeller maximize

    S_rho(A) = sum_i <1_Ai,T_rho 1_Ai> - sum_i gamma(A_i)^2

for EVERY finite measurable Gaussian partition, in EVERY dimension d>=2, with EVERY finite number k>=3 of labels, allowing empty cells and arbitrary masses, and EVERY 0<rho<=rho_0. This question is not answered here. No three-label, bounded-dimension, asymptotic-only or local replacement is nominated. In particular this is not another claim of first-moment propeller stability.

## Strongest inputs used

Pinned source096, `ext:duality` and `ext:structure`, already supplies Gaussian score duality, attainment, minimal-label merging, strict negative centroid products, the Gram-Laplacian rank calculation, and conical reduction for the FIRST-MOMENT objective. Its main theorem gives B^2=9/(8 pi), with B=3/(2 sqrt(2 pi)). These statements and operations are stipulated, not truth-audited.

The actual I38 proof, Sections6.2–7, is stronger than its distance headline. For every partition with first-moment deficit Delta=B^2-sum_i|z(A_i)|^2 it chooses a unit equilateral score array t=(t_1,t_2,t_3,0,...) and proves

    J = E[max_i <t_i,G> - <t_{A(G)},G>] <= C Delta.           (1)

The constant is independent of dimension and label count. In particular it controls weighted score loss, not just disagreement probability. Its preceding compactification, extra-score estimate, polar alignment, and exact squared-distance identity are credited historical operations. They are not reconstructed or nominated in this round. The associated propeller P has z(P_i)=B t_i. Labels and plane in the following calculation are those of such a P, or any fixed propeller when (1) is not needed.

The strongest primary comparison is Heilman, [2306.03312v3](https://arxiv.org/pdf/2306.03312v3), actual Section8 equations(46)–(53), Corollary4.2 and Lemma5.1, together with Heilman–Tarter [2011.05583v2](https://arxiv.org/pdf/2011.05583v2), Lemmas5.4–5.5 and the complete Section6 proof of Theorem1.9. The latter uses translation almost-eigenfunctions, the volume-preserving kernel and a positive second variation to reduce an m-cell maximizer to dimension m-1. It does NOT reduce arbitrary m to three or to a plane.

Heilman's positive-correlation theorem is stated for three equal masses, but its actual radial proof has a more compatible centered interface. This matters and was checked before any selection. Let g(r) be the vector of circular masses, m=Eg, c=(1/3,1/3,1/3), and phi(r)=1-exp(-rho r/2). The angular comparison in (50) subtracts .109 E[phi|g-c|^2]. After subtracting |m|^2, the other term is the radial covariance, to which Lemma5.1 applies centered at m. With W=E[phi|g-c|^2],

    E[phi|g-m|^2] <= 2(1+E phi E(1/phi)) W.

Indeed weighted Cauchy–Schwarz bounds |m-c|^2 by E(1/phi)W. For planar Gaussian radius R,

    E phi <= (rho/2) E R,
    E(1/phi) <= 1+(2/rho) E(1/R),
    E R = E(1/R) = sqrt(pi/2).

Thus E phi E(1/phi)<2 for rho<=1/10, and the centering costs at most6. The primary radial estimate is then at most15(rho+rho^2)W. At a sufficiently small absolute rho this is absorbed by its existing angular penalty. Fixed-mass dimension reduction applies before this comparison since subtracting the fixed squared masses changes no optimizer. This calculation identifies a compatible THREE-CELL reduction in the actual primary proof; it is not proposed as a new full result. The primary's numerical inequalities and angular rearrangement are credited inputs, not independently certified numerical claims here. The full helper chain was not reread; precise extents are in reading-limits.md.

## Global entry is already cheap

Write Pi_m for Gaussian Hermite projection of total degree m. Then

    S_rho(A)=sum_(m>=1) rho^m sum_i ||Pi_m 1_Ai||_2^2.

All terms are nonnegative. The entire squared norm budget is 1. If S_rho(A)>=S_rho(P), the source first-moment inequality gives Delta<=rho. The historical stability estimate therefore places A within O(sqrt(rho)) disagreement of some propeller, uniformly in dimension and label count. This only gives entry into a neighborhood; it does not prove optimality at any fixed positive rho.

## A quadratic higher-mode estimate

The following calculation was completed as feasibility. It is NOT a replacement nominee. It addresses the quadratic perturbation term only.

Decompose R^d=R^2_u x R^(d-2)_z using the propeller plane. Let L_1,L_2,L_3 be the full lines containing its three boundary rays, and set

    w(u)=min_j dist(u,L_j).

There is an absolute finite C such that, for every d>=2, every measurable f:R^d->[-1,1], and 0<rho<=1/4,

    sum_(m>=2) rho^m ||Pi_m f||_2^2
        <= C rho^2 integral w(u)|f(u,z)| dgamma_d.           (2)

Here is a general proof, including arbitrary dependence on z.

First let 0<a<1/4, W(t)=exp(a t^2), and 0<=h<=1 on the real line. For all lambda>0,

    integral_{|t|/W(t)<=lambda} W(t) dgamma_1(t) <= K_a lambda,
    K_a = sqrt(2/pi) exp(2a) + E exp(2a G^2) < infinity.

On |t|<=1, the set is contained in |t|<=lambda exp(a), and W<=exp(a). On |t|>1, its indicator times W is bounded by lambda W^2/|t|<=lambda W^2. This proves the displayed bound without a bounded-support assumption. Splitting the integral of Wh at that same set gives

    integral Wh <= K_a lambda + lambda^(-1) integral |t|h.

Optimization over lambda yields (integral Wh)^2<=4K_a integral |t|h, including the zero-integral case by a limit.

For 0<=h(u)<=1 in the plane, split h into three measurable pieces according to a nearest L_j, breaking ties measurably. On the j-th piece choose orthogonal coordinates (t,s) normal and tangent to L_j. Apply the one-dimensional bound for each s and then Cauchy–Schwarz in s with exp(a s^2). Summing the three pieces gives

    (integral exp(a|u|^2)h(u) dgamma_2)^2
       <= 12 K_a E exp(2a G^2) integral w(u)h(u) dgamma_2.   (3)

For q=1/4 the Mehler kernel with respect to gamma_2 has diagonal

    K_q(u,u)=(1-q^2)^(-1) exp(q|u|^2/(1+q)).

Its positive Hermite feature representation and the Hilbert-space triangle inequality imply

    <f,T_q^(u) f>_(gamma_2)
       <= (integral |f(u)| sqrt(K_q(u,u)) dgamma_2)^2
       <= C_q integral w(u)|f(u)| dgamma_2,                 (4)

by (3) with a=q/(2(1+q))=1/10. This also follows first for finite Hermite projections and then by monotone convergence; all majorants used in (3) are integrable.

Expand the full f in the orthonormal product Hermite basis, with coefficients c_(alpha,beta). For |alpha|+|beta|>=2 and rho<=q<1,

    rho^(|alpha|+|beta|) <= (rho/q)^2 q^|alpha|.

For |alpha|>=2 use rho^(|alpha|-2)<=q^(|alpha|-2); for |alpha|=1 use |beta|>=1; for |alpha|=0 use |beta|>=2. Parseval in z and (4) on each fiber now prove (2). Constants do not depend on d or on the number of scalar functions to which it is applied.

Put f_i=1_Ai-1_Pi. Every mismatch contributes two units to sum_i|f_i|. For an incorrect active label, the score gap is distance to one of the full boundary lines; for an inactive label, max_i<t_i,u>>=|u|/(2sqrt(3)). Consequently

    sum_i integral w|f_i| <= 4sqrt(3) J.

Summing (2) gives the favorable bound

    0 <= sum_i <f_i,(T_rho-Pi_0-rho Pi_1)f_i> <= C rho^2 J. (5)

Thus the quadratic higher-mode term can be bounded without a label-count union bound, finite-dimensional surrogate, or independence of the tangential coordinates. The proof uses classical Mehler/Hermite operations. No contribution rating is attached to it.

## The linear term prevents closure of this argument

Let R_rho=T_rho-Pi_0-rho Pi_1. The exact difference is

    S_rho(A)-S_rho(P)
      = -rho Delta + 2 sum_i <f_i,R_rho 1_Pi>
                    + sum_i <f_i,R_rho f_i>.                (6)

Equations(1) and(5) pay the last term. They do not pay the middle term. It is not legitimate to use a Taylor expansion on a fixed planar ball and then silently discard the rest.

For a ray u=Re in the strict interior of P_1, and a different active label2, write ell_i(u)=<z(P_i),u>. At fixed rho>0,

    T_rho 1_P1(Re) -> 1,     T_rho 1_P2(Re) -> 0,
    R_rho 1_P1(Re)-R_rho 1_P2(Re)
         = 1-rho(ell_1(Re)-ell_2(Re))+o(1).

Here ell_1(Re)-ell_2(Re)=cR with c>0. Therefore the absolute ratio of this remainder to the score gap tends to rho, not O(rho^2) with a constant uniform as rho decreases. Swapping a sufficiently small ball near Re from label1 to label2 realizes the same obstruction for the integrated absolute-error comparison. It is a method diagnostic only: the FULL smoothed score difference tends to1 and penalizes that swap. The example does not refute the proposed noise-stability question.

One would need a simultaneous comparison using the actual bounded smoothed score margins, the centroid/alignment term, and extra-label redistribution, while retaining Gaussian tails and all tangential dependence. The existing three-cell angular proof and m-1 dimensional reduction do not eliminate the arbitrarily many extra cells. Whole-cell merging is not enough either: a small central disk assigned to an extra label can have negative centered covariance with EACH remaining sector, even though redistributing it among the sectors has a different effect.

No such full comparison was completed here. The exact unresolved operation is this global nonlinear margin/alignment and extra-label comparison for the centered functional at fixed positive rho. Neither (2), a planar three-cell conclusion, nor the rho->0 entry estimate is nominated. No full-target counterexample, acceptance, substantiality judgment, or independent mathematical gate is asserted.
