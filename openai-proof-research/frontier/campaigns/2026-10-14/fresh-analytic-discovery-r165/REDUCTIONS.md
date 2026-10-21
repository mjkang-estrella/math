# Complete numerical-range calculus and the location of a sharp metric

PREFREEZE / no nominee. These are author feasibility derivations, not an independently reviewed theorem. Codex / GPT-6 Astra / high / default service tier. The supplied campaign remains 19/20, latest R041; parent alone adopts grades and counts. No formal, manuscript or release stage is opened.

## 1. Exact prospective full scope

For every element a of a nonzero unital C*-algebra, put B=C*(1,a), and let K={omega(a): omega is a state of B}. Let Omega be any bounded open convex domain with regular real-analytic Jordan boundary and K contained in Omega. Let f:Omega->D be an interior conformal bijection with the source's univalent collar. The prospective question is whether there must exist h in B with

 1 <= h <= 4*1,        f(a)* h f(a) <= h.                 (I)

All numerical ranges here are state numerical ranges; in a faithful Hilbert representation their values are the closure of the vector numerical range. A scalar state extends to the ambient bounded-operator algebra, so the support-function descriptions agree. In the universal representation this agreement is immediate from the GNS vector of each state. K is compact convex. Its compact containment in the open Omega is part of the scope, not an extra spectral-gap condition added later.

This is not a frozen theorem, an assertion that (I) is new, or a counterexample claim. It is distinct from the old full targets on equality, scalarization, polynomial disk geometry and quantitative annuli. None of those scopes is restricted or renamed. The issue is the location h in C*(1,a), not the already-paid external similarity, complete spectral-set estimate, matrix amplification or ordinary common density.

A first correction to a tempting reduction is essential: C*(1,a) is separable, even if the original representation Hilbert space is not. That does not imply that B is nuclear, that its universal bidual is injective, or that external similarities can be averaged into B**. No such implication is used.

## 2. What both actual source proofs already pay

D denotes the pinned direct proof and S the structural proof. D Theorem main covers all finite base and coefficient dimensions independently. Its operative chain is the positive double-layer resolvent; the two-marginal Faber kernel; Hilbert-Schmidt coefficient duality; BOTH ordered tests FG and GF; and the positive block trace comparison. S constructs the optimal finite metric by strict feasibility and separation, realizes a matrix-valued rational endpoint extremal, and compares two different densities. Its original-matrix density has mass 2; its similar-matrix density has mass 1. Substituting one for the other is invalid.

S Corollary hilbert already pays complete polynomial, rational and holomorphic bounds on arbitrary Hilbert spaces. The one metric and one continuous positive density are stated for finite base matrices, but their extension to arbitrary Hilbert spaces under strict enclosing geometry is also paid by the compatible construction in the next section. Calling that extension alone substantial would not isolate a new operation.

Actual primary DD gives a positive boundary measure, its Carl Neumann correction and the contractive disk density. BCD gives the dilation/similarity route, exact disk constant two and explicit two-dimensional conformal similarity. LS keeps the commuting scalar correction through all powers; it expressly does not make that argument a complete proof. HM uses matrix Potapov transforms and asymptotic coefficient orthogonality to remove a scalar functional correction at every matrix level. ACV supplies square-function Stein metrics and treats noncommutative corrections with explicit counterexamples and conditional diagonal averaging. These operations have been integrated below rather than inferred from their titles.

## 3. External strict metrics on arbitrary Hilbert spaces

Represent B faithfully on H. Choose Omega_1 analytic convex with K subset Omega_1 and closure Omega_1 subset Omega; the actual source outer-approximation lemma supplies it. Fix z0 in Omega_1 and set q=max_closure(Omega_1)|f|<1. For each finite-dimensional E subset H, put

 a_E=P_E a P_E + z0(I-P_E).

Its finite block has W(P_E a|E) subset K. Apply S to this finite block and Omega_1, obtaining 1<=h_E<=4 and a similarity making g(P_E a|E) contractive, where g maps Omega_1 to D. The SAME common boundary representation evaluates f, giving

 f(a_E)* h_E f(a_E) <= q^2 h_E.                         (2)

Here h_E is extended by I on E-perp; the scalar complementary block satisfies |f(z0)|<=q. This step invokes the full compatible representation rather than falsely identifying f with g or assuming numerical-range containment survives similarity.

The directed net of all E has P_E->I strongly. Thus a_E->a strongly and a_E*->a* strongly, uniformly bounded. Choose a fixed analytic convex contour enclosing K union {z0} inside Omega_1. Numerical-range separation gives a uniform bound for (z-a_E)^(-1) on it. The resolvent identity gives strong convergence on that contour, uniformly on its compact parameter after a finite net argument. Norm-bounded contour integration gives f(a_E)->f(a) strongly, and conjugate-adjoint contours give strong convergence of the adjoints.

The order interval [I,4I] is weak-operator compact, so a subnet of h_E converges weakly to h_ext. For every x, the difference between <h_E f(a_E)x,f(a_E)x> and <h_E f(a)x,f(a)x> tends to zero, since ||h_E||<=4. The remaining term converges by weak convergence. Consequently

 I<=h_ext<=4I,       t* h_ext t<=q^2 h_ext,   t=f(a).    (3)

This proves the external construction directly from the actual finite source, without treating inaccessible Paulsen text as if read. No separability, norm-attainment or finite-dimensional spectral decomposition of a is used.

## 4. Strict endpoints and a uniform local reserve

Put d=1-q^2 and M=||t||. Choose eta>0 with eta<min(1/4,d/[4(1+M^2)]), and set

 k=(1-eta)h_ext+(5eta/2)I.

Then mI<=k<=uI, where m=1+3eta/2 and u=4-3eta/2. Moreover

 k-t*k t
 >= (1-eta)d I +(5eta/2)(I-t*t)
 >= [(1-eta)d -(5eta/2)max(M^2-1,0)]I
 >= (d/8)I.                                           (4)

The convex centering leaves room at BOTH endpoints and in the Stein inequality. The weaker statement that t has spectral radius below one would not by itself give the sharp endpoint interval; (3) is what supplies it.

The same k is feasible for all t' sufficiently close to t. In fact

 ||t'*k t'-t*k t|| <= ||k|| (2M||t'-t||+||t'-t||^2).    (5)

Thus a fixed neighborhood with the right side below d/16 retains strict positivity. This local reserve, not differentiability of the optimal SDP metric, is enough for continuous gluing whenever internal metrics are available.

## 5. A norm-convergent internal Stein series with explicit cost

For t=f(a), r=max_K|f|<1. Spectral mapping gives r(t)<=r. The series

 h0=sum_(j=0)^infinity t*^j t^j                         (6)

converges in norm in B, and h0-t*h0 t=1. Convergence also follows directly from the complete bound ||t^j||<=2r^j for j>=1 (when r=0, scalar holomorphic evaluation forces t=0). The complete column test, padded to a square coefficient matrix, gives

 1<=h0<=L*1,    L=1+4r^2/(1-r^2).                     (7)

Indeed, for the finite tail column (f,...,f^N), the square of its evaluation norm is ||sum_(j=1)^N t*^j t^j||, and its squared boundary norm is at most sum r^(2j). Add the exact identity term instead of losing a factor four there. Passing to the norm limit proves (7).

Thus there is ALWAYS some internal similarity to a contraction at this scope. What is unproved is the sharp cost two, not existence of an internal similarity. For r^2<=3/7, (7) itself already gives h0<=4. This is a paid small-image case and is not a restricted nominee. For larger r this estimate loses the desired constant; its failure is not a lower bound on the true optimal cost.

### Late primary strengthening of the internal series

After the first notebook draft, the full ACV Section 3 sampling proof and its exact Theorem 1.5 were read. This is a late read, not backdated. For F=f/r, that primary proves

 P_tau=sum_(j>=0) tau^(2j) F(a)*^j F(a)^j <= (1-tau)^(-1)1.

Its proof uses a positive ball kernel, the extra sample at zero cancelling the antiholomorphic correction, a matrix inequality for a diagonalization, and then perturbation and Krylov compression. Norm convergence is obtained by comparing tau with a larger sigma<1. Thus its applicability includes our arbitrary represented a and holomorphic F; this is an actual stronger operation than merely summing the complete norm bound.

At tau=r the series is h0 itself, improving its repair bound to

 L0=min(1+4r^2/(1-r^2),1/(1-r)).

More significantly, at tau=r^2 put

 k_r=sum_(j>=0) r^(2j) t*^j t^j.

Then 1<=k_r<=(1-r^2)^(-1)1, and the exact Stein identity yields

 t*k_r t=r^(-2)(k_r-1)<=k_r.

Consequently an INTERNAL sharp-two metric is already paid whenever r<=sqrt(3)/2. For r^2<=1/2, ACV Corollary 3.7 further gives k_r<=1+4r^4. At r=0 use t=0 and k_r=1. These are improvements of the reduction, not restricted nominees. In particular the earlier 3/7 threshold was not the strongest final comparison. For r approaching one, this family still supplies no constant-two bound; no optimality of this one-parameter family is claimed.

## 6. Bidual localization plus convex approximation closes the strict case

This section explicitly assumes a unital positive B-bimodule map

 E:B(H_u)->B**,

where pi_u is the UNIVERSAL representation of B and B**=pi_u(B)''. This extra assumption is not asserted for every B. Apply the preceding external construction in H_u. Bimodularity and positivity transfer (4) to k**=E(k):

 m1<=k**<=u1,       k**-t*k**t>=s1,  s=d/8>0.          (8)

Here is the full passage back to B, including the topology.

The interval [m1,u1] in B_sa is weak*-dense in the same interval in B**_sa. After affine rescaling this is Goldstine for the real selfadjoint unit ball; a separating selfadjoint functional would otherwise contradict equality of its norm on B and B**. Likewise the bounded positive interval containing k**-t*k**t-s1 can be approximated weak* by positive elements of B.

Let
 C={b-t*bt-p: b in B_sa, m1<=b<=u1, p in B_+}.

This set is convex. The two preceding approximations put s1 in its weak* closure inside B**. Since the limit s1 belongs to B and the continuous linear functionals used are all of B*, Hahn-Banach separation implies s1 lies in the NORM closure of C. This is exactly where the universal bidual matters; strong density in an arbitrary represented closure does not furnish the topology sigma(B,B*).

Choose b,p with ||b-t*bt-p-s1||<s/2. As the error is selfadjoint,

 m1<=b<=u1,     b-t*bt>=s1/2.                          (9)

Thus b is an internal metric satisfying (I), with strict endpoint and Stein slack. No limiting internal metric has been asserted to exist; we selected one sufficiently accurate norm approximation. Strictness pays the entire final step.

For comparison, if one has only a nonstrict bidual metric 1<=h**<=4, the identical convex argument gives b in [1,4] with b-t*bt>=-epsilon*1. The explicit repair

 b_epsilon=b+epsilon h0

then satisfies b_epsilon-t*b_epsilon t>=0 and

 1<=b_epsilon<=(4+epsilon L0)1.                         (10)

This gives internal costs arbitrarily close to two, conditional on that bidual metric. It does NOT establish exact attainment when both endpoint and Stein reserves vanish. Formula (10) is a concrete correction, not an unjustified norm limit of h**.

## 7. Finite algebras and continuous matrix fields need no new operation

For a finite-dimensional B, decompose it into matrix summands and use the source metric in each summand normalized to [1,4]. Alternatively, in any representation B acts as a finite direct sum of M_n tensor I; pinch to these summands and apply a state on each multiplicity factor to obtain the required unital positive bimodule map. Section 4 gives simultaneous strict reserves.

For B=C(X,M_n), with X compact Hausdorff and K contained in Omega, there is a direct construction. At each x choose a strict finite-source metric for a(x). By (5), that constant matrix works on a neighborhood of x. Take a finite partition of unity subordinate to a finite cover and set h(x)=sum phi_i(x)h_i. Every h_i contributing at x is feasible for that SAME t(x), and the inequality is linear in h. Thus h is continuous, 1<h<4, and h-t*ht>0. Compactness gives positive uniform reserves. The same argument works for a paracompact base with a locally finite partition and pointwise reserves.

This is not a claim that the optimizer itself is continuous or unique. It establishes the existence of a continuous SHARP-BOUND metric by gluing strict feasible choices. It pays that tempting parameter-family extension without differentiating KKT equations. This field statement is about the full ambient algebra C(X,M_n). To infer membership in C*(1,a), that generated algebra must equal the field algebra, or a separate localization such as Section 6 must apply. No membership in a smaller constrained subalgebra follows just from the partition of unity.

## 8. One internal boundary density, when the internal metric is obtained

Let b be any internal feasible metric and D=b^(1/2)t b^(-1/2). Then D*D<=1 and r(D)<1. Define for |zeta|=1

 Phi_D(zeta)=(1-D/zeta)^(-1)+(1-D/zeta)^(-1)*-1
            =(1-D/zeta)^(-1)* (1-D*D) (1-D/zeta)^(-1).

The identity is checked by congruence with 1-D/zeta. Every factor belongs to B, and the field is positive and norm-continuous. Its uniformly convergent Fourier series is

 Phi_D=1+sum_(j>=1)(zeta^(-j)D^j+zeta^j D*^j).

For exterior coordinate G of Omega, psi=f composed with G and positive angular Jacobian j, set Lambda(t)=j(t)Phi_D(psi(t)). It has Bochner integral 1 in B and represents every finite matrix-valued v holomorphic near closure Omega:

 v[b^(1/2)a b^(-1/2)] = integral Lambda(t) tensor v(G(t)) d tau.

The same b and Lambda work for every coefficient dimension and function. The norm estimate is the source compression bound multiplied by cond(b^(1/2))<=2. In a representation use the isometry x->Lambda^(1/2)x; faithfulness returns the identity to B. Finite tensoring, holomorphic approximation and continuous dependence with strict reserves are all paid. None is a nominee.

## 9. An exact intrinsic dual problem, without assuming an internal optimizer

Let t in a unital C*-algebra B satisfy r(t)<1, and define

 p_B(t)=inf{tau: 1<=h<=tau*1, h-t*ht>=0, h in B_sa}.

The set is nonempty by (6), and the three slacks have a strictly positive common witness: use c h0 with c>1 and tau>c||h0||. The following dual reduction does not assume the infimum is attained.

In the real Banach space R plus B_sa^3 separate the affine set

 A={(s,h-1,s1-h,h-t*ht):s real,h selfadjoint}

from the open convex set O={(s,U,V,W):s<p_B(t), U,V,W strictly positive}. The affine set is disjoint from O by definition. Continuous separation gives a nonzero functional

 ell(s,U,V,W)=lambda*s-beta(U)-alpha(V)-phi(W),

with lambda>=0 and positive continuous functionals alpha,beta,phi. Boundedness above on O forces these signs. If lambda=0, evaluation at the strictly feasible witness makes ell strictly negative, while sup_O ell=0; this contradicts separation. Normalize lambda=1.

Constancy on the affine set gives

 alpha(1)=1,
 alpha-beta=phi-phi composed with L_t,    L_t(h)=t*ht.   (11)

The constant value is beta(1)>=p_B(t). Evaluating at any feasible (tau,h) gives

 beta(1)=tau-beta(h-1)-alpha(tau1-h)-phi(h-t*ht)<=tau.

Taking the infimum proves beta(1)=p_B(t). Conversely any positive triple satisfying (11) has beta(1)<=every feasible tau. Therefore

 p_B(t)=max beta(1) over positive triples in (11).       (12)

For completeness, the affine set is closed (h is recovered continuously from its second coordinate), though separation only needs one of the two sets open. Constancy follows by varying s,h over all real directions. No finite-dimensional trace, compact optimizer or endpoint eigenspace was smuggled into this duality.

The positive phi has an automatic bound: apply (11) to h0 to obtain

 phi(1)=alpha(h0)-beta(h0)<=||h0||<=L0.                  (13)

Since r(L_t)=r(t)^2<1, its inverse Stein series converges in operator norm and

 phi=sum_(j>=0)(alpha-beta) composed with L_t^j.        (14)

Thus the remaining sharp estimate is a definite inequality about positive functionals, not an unspecified search for a similarity. At the prospective scope, proving beta(1)<=4 for EVERY triple in (11) would prove p_B(f(a))<=4. An infimum bound by itself need not attain four, but strict enclosing geometry supplies the reserve: establish the bound first for g(a), where g maps Omega_1 to D, obtain arbitrarily near-four feasible metrics there, transfer f via the contraction calculus, center as in Section 4, and choose the approximation close enough that the upper endpoint drops below four. This last interpolation does not need exact four-attainment for g(a).

## 10. Why the finite endpoint realization does not yet pay (12)

For matrices the source represents alpha,beta,phi by positive trace-class matrices, identifies supports using an actual minimizing metric, factors a finite operator equality, and constructs a rational matrix Schur extremal. The current (11) is an identity of functionals on ALL of B. In a GNS representation it is an identity of vector functionals, not the finite matrix equality XX*-YY*=Q-DQD*. Replacing it by that equality in B(H_u) is not justified.

One possible route is to realize (11) as a colligation with coefficients in a commutant and to prove a relative coefficient calculus. The needed form would control sum pi(a)^j C_j for commuting coefficient operators C_j in pi(B)' by 2 sup_(z in K)||sum z^j C_j||. The ordinary finite matrix-valued source bound is a spatial tensor statement. It does not, merely by its wording, give this relative statement in an arbitrary commuting representation. No equivalence between this relative bound and (I), and no counterexample to either, has been proved here.

Another possible route is to repeat the positive-block proof with states. Its trace cyclicity cannot simply be removed. For the positive scalar matrix Delta=[[1,2],[2,4]] and J=diag(1,-1),

 Delta J Delta J=[[-3,6],[-6,12]].

Its ordinary trace is 9>=0, as the source requires. Its vector state at e1 is -3. Thus the replacement of the full trace by an arbitrary positive functional fails even in this elementary diagnostic. The identity using Delta^(1/2)JDelta^(1/2) is positive, but relating it back to separated diagonal and off-diagonal square norms requires the cyclic trace operation. This does not refute the intrinsic theorem: finite algebras already satisfy it by Section 7. It only blocks this particular transplanted proof step.

The source statement is stipulated true. These failures concern NEW applicability claims, never an audit of that source.

## 11. A concrete compactness diagnostic and the remaining obligation

Let a=diag(1,1/2,1/3,...) on ell2 and B=C*(I,a). Elements of B are exactly the convergent diagonal sequences. Let h_N have its first N diagonal entries equal to 1 on odd positions and 4 on even positions, and all later entries equal to 2. Then h_N in B, 1<=h_N<=4, and a*h_N a<=h_N. They converge strongly to the alternating diagonal sequence h_infinity, which is not in B. Thus even a strong limit of uniformly bounded internal feasible metrics need not remain internal. In this example I is a perfectly good internal solution; it is a diagnostic of the limiting inference, not a counterexample to existence.

The unrestricted remaining operation is now precise: bound beta(1) by four in (11) for t=g(a) using the numerical-range structure, WITHOUT assuming an expectation into B**, or supply another intrinsic construction at the same full scope. Section 9 explains how strict enclosure then pays exact four-attainment and Sections 5–8 pay the repair, regularity and common density. We have neither the general dual bound nor a counterexample to it. The relative-coefficient route is still only a possible route and cannot be asserted as an established equivalence.

The completed external, conditional internal, continuous-field, repair and duality calculations are compatible compositions and reductions. They are retained for further work, not labelled as a substantial finding. The inaccessible original Paulsen paper and bounded primary/history reading prevent any universal priority or exhaustive-clearance claim. No viable complete substantial theorem has been frozen; final disposition is PREFREEZE/no nominee.
