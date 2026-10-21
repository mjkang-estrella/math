# PREFREEZE transport derivation — no nominee

This is exploratory mathematics, not a frozen theorem or a contribution verdict. Pin and operative proofs are stipulated. Only Source374 receives sustained work; log-concave functional inequalities received initial catalogue navigation only. No new family after overlap.

## 1. Candidate operation: move the source as well as the target

Let rho be uniform on a fixed convex body K, mu supported in a fixed ball, and T the rho-to-mu Brenier map. Let sigma be another source, pi an optimal sigma-to-mu plan (possibly nondeterministic), and gamma a coupling of rho,sigma. Glue gamma to pi by the sigma coordinate, writing random variables X,Z,Y, with X~rho, Z~sigma, (Z,Y)~pi. Put U=T(X), D^2=E|U-Y|^2, and w^2=E|X-Z|^2. All variables have finite second moment, targets bounded.

Use the correlation gaps (half the squared-cost excess):

G0=E[X dot (U-Y)] >=0,
G1=E[Z dot (Y-U)] >=0.

Both competitors have correct marginals. Thus

G0+G1=E[(X-Z) dot (U-Y)] <= w D.

A bounded-density, bounded-target plan-conditioning inequality of the form D^4 <= A G0 immediately gives D^3 <= A w (including D=0 separately). This is an exact compatible composition, not the looser bound G0 <= 2L E|X-Z|. It requires no regularity of sigma and no deterministic pi. With an optimal source coupling, w=W2(rho,sigma). It bounds the lifted discrepancy for the specified gluing, hence a coupling distance of the two optimal graph plans as well. The direct source perturbation exponent is 1/3. Primary proof comparison is pending, and this elementary self-improvement must not be charged as a nonroutine operation merely because the quantifiers are broad.

For changing targets, insert the optimal rho-to-nu map. Pinned Source374 pays the common-source target change with exponent 1/3. Minkowski then combines it with the source step, with constants uniform over bounded targets. This composition would produce a full joint estimate if the conditioning interface is established at its true hypotheses; it is not an additional proof-feasible novelty claim.

## 2. Localized convex source perturbation: potential sharpness

On K=[-1,1]^2 with uniform rho, choose a smooth odd compactly supported h on (-1,1), with h'(0)>0. Let k(y)=y initially, and set

Psi_a(x,y)=(x^2+y^2)/2 + epsilon a^2 h(x/a) k(y),
S_a=grad Psi_a,
sigma_a=(S_a)#rho,
mu=(delta_{-e1}+delta_{e1})/2.

The Hessian perturbation has entries epsilon h''(x/a)k(y), epsilon a h'(x/a)k'(y), epsilon a^2 h(x/a)k''(y). Fix epsilon small independently of a so Psi_a is uniformly strongly convex on a neighborhood of K (and can be extended convexly). Therefore S_a is the optimal rho-to-sigma_a map. Central symmetry of h odd and k odd makes sigma_a centrally symmetric, so T^{sigma_a}_mu(z)=sign(z1)e1. Also T^{rho}_mu(x,y)=sign(x)e1.

The displacement is supported on |x|<a and has horizontal size O(a), vertical O(a^2), so W2(rho,sigma_a)^2 is comparable to a^3. On a rectangle with y bounded away from zero and x in a short interval of length comparable to a just across zero, h'(x/a) stays positive and the sign of S_a,1 differs from the sign of x. Thus the squared lifted map discrepancy is comparable to a. This would make exponent 1/3 sharp for maps compared through optimal source coupling, already with fixed two-atom target and source densities comparable on their supports.

To keep the source support EXACTLY K, replace k by an odd smooth function supported in (-1,1), positive on an interior y interval. The perturbation then vanishes near every boundary face; S_a is identity there and a strongly monotone diffeomorphism K onto K. Its Jacobian determinant remains uniformly positive/bounded. The same sign argument and central symmetry still apply. Hence both sources can have uniformly positive smooth densities on the same cube. This is a preliminary feasibility calculation; no scope is frozen, and classical/primary duplication is still unresolved.

## 3. Known history boundary

Actual I33/I34 and r12 original scopes concern common-source target changes, including density-robust Q and log-concave LC. They are not solved by the source-coupling estimate above. The weighted moment failure and linear potential failure of I33 do not refute Q. The special coupling for source perturbation has a cancellation involving BOTH optimality gaps; for different targets the cross competitors do not have the requisite marginals. One cannot silently use this cancellation to prove the old Q.

## 4. Strongest primary composition, now checked in actual bodies

Ford, arXiv:2609.35574v1, body.tex `thrm: quant reg` and `lem: Fenchel bound distance`, give an operative proof of the conditioning input above. For bounded density rho on B_R and a globally convex L-Lipschitz u, write Osc_s u(x)=diam partial u(B_s(x)). The proof gives integral Osc_s u drho <= C s (0<s<=1). If U=grad u(X) and Y has the same target law, then

|Y-U| <= Osc_s u(X) + [u(X)+u*(Y)-X dot Y]/s.

Since |Y-U|<=2L, integration gives D^2 <= 2L(Cs+G0/s). Choose s=sqrt(G0) when 0<G0<=1; if G0>1 the trivial D<=2L absorbs it, and if G0=0 let s decrease to zero. Thus D^4<=A G0 with A depending only on fixed source radius/density and target radius. The integrated Fenchel gap equals G0 because Y and U have the same law. No lower source density, atom count or quantitative inverse cell Laplacian is needed. Ford's displayed general-marginal statement is in W1 and has a quarter power; the stronger fixed-target composition here uses its actual conditioning proof plus G0+G1<=wD, not an incorrect claim that its theorem states the cube-root result.

The two-gap cancellation is elementary optimality with feasible cross competitors. It proves the source-displacement estimate already at bounded-density scope, beyond the initially uniform reference. It therefore supplies no missing weighted-moment estimate for I33.

There is also a common-coordinate bound. Let v be a globally convex L-Lipschitz potential for sigma-to-mu, and V=grad v(X). Even if sigma is singular, the disintegrated Y is in partial v(Z) almost surely. On |X-Z|<=s, |V-Y|<=Osc_s v(X); otherwise it is <=2L. The q=2 oscillation estimate and Markov give

E|V-Y|^2 <= C s +4L^2 w^2/s^2.

Choose s=w^(2/3) for 0<w<=1, with trivial large-w and limit-zero cases. This is precisely the operative same-subgradient proof of Carlier--Delalande--Merigot 2401.01088v1 (p=q=r=2) and Ford's same-subgradient proof, not a new regularity principle. Minkowski with Section 1 gives ||grad u-grad v||_L2(rho) <= C w^(1/3). It requires selecting v with globally bounded slopes; no classical theorem is applied to an unrestricted arbitrary extension.

Adding Source374's target estimate to either source comparison is an explicit compatible route to joint source/target cube-root control at the uniform-reference scope. This algebra, the same-subgradient coupling, and the known conditioning operation account for the whole proposed upper estimate. No theorem is frozen or nominated on that basis.

## 5. Keep three different comparison quantities separate

(a) Common-coordinate map error: ||T_rho(x)-grad v_sigma(x)||_L2(rho).
(b) Source-aligned discrepancy: E|T_rho(X)-Y|^2 under a fixed optimal source coupling and an optimal sigma-target plan.
(c) W2 distance of graph plans on the product space, minimized over ALL couplings of those plans.

The argument above bounds (a),(b) by a cube root. It bounds (c) from above by (w^2+D^2)^(1/2). A lower bound for (a) or (b) DOES NOT lower-bound (c). This matters when looking for a genuinely additional operation.

For an exact scaling check for (a), let rho be uniform on [-1,1]^d, choose b in C_c^infinity((-1,1)) nonnegative with b(0)=1, and fix epsilon>0 so epsilon||b'||_infty<1/2. Set

S_a(x)=(x1+epsilon a b(x1/a), x2,...,xd), 0<a<1/2.

S_a is the gradient of a smooth strongly convex function, is identity off the slab |x1|<a, and maps the cube onto itself. The Jacobian is in [1/2,3/2]; its pushforward sigma_a has a smooth interior density uniformly comparable with rho. With the fixed equally weighted target at +/-e1, its median threshold is epsilon a, so

T_rho(x)=sign(x1)e1,
T_sigma(z)=sign(z1-epsilon a)e1,
W2(rho,sigma_a)^2=(epsilon^2 a^3/2) integral_{-1}^1 b(s)^2 ds,
||T_rho-T_sigma||_L2(rho)^2=2 epsilon a.

Thus the common-coordinate cube-root scaling survives uniformly positive smooth densities on the same cube. However T_sigma(S_a(x))=T_rho(x): here the natural source-aligned discrepancy is ZERO and the graph-plan W2 distance is EXACTLY W2(rho,sigma_a), by the induced coupling and projection lower bound. The common-coordinate sharpness cannot certify graph-plan sharpness.

For (b), use the h,k construction of Section 2 with h odd and h(s)=s on |s|<=1/4, h supported in (-1,1), and k odd, nonzero, smooth and supported in (-1,1), with y k(y)>=0. Fix epsilon small enough that the global Hessian of Psi_a lies between I/2 and 3I/2 for every 0<a<1/2, and epsilon||k||<=1/8. A strongly monotone global diffeomorphism equal to the identity outside an interior rectangle maps the square onto itself: any exterior point is fixed and injectivity excludes an interior preimage of it; surjectivity gives the converse. Hence sigma_a again has a smooth interior density with fixed upper/lower bounds on the SAME square.

Central symmetry gives the same fixed two-atom target and the same pointwise map sign(z1)e1 for rho and sigma_a. For each y the strictly increasing function S_a,1(x,y) has its unique zero at x=-epsilon a k(y), inside the region h'=1. Consequently the aligned discrepancy and displacement satisfy the exact formulas

D_a^2=epsilon a integral |k(y)|dy,
w_a^2=(epsilon^2 a^3/4)(integral h'(s)^2 ds)(integral k(y)^2 dy)
      +(epsilon^2 a^5/4)(integral h(s)^2 ds)(integral k'(y)^2 dy).

Again D_a has cube-root scaling in w_a, while the common-coordinate map difference is ZERO. These are elementary localization calculations, not a substantial-contribution nomination.

## 6. Actual residual: optimize the graph coupling with fixed target

The more interesting operation would improve the source-only graph-plan estimate by optimizing the coupling instead of fixing its source projection. At the initial uniform-reference scope, the integrated derivation only proves

W2((id,T_rho)#rho, pi_sigma) <= (w^2+Cw^(2/3))^(1/2),

for fixed compact target mu, arbitrary sigma on the fixed compact source container, and any optimal pi_sigma. No sharper modulus is established here. In particular a prospective square-root upper bound would require constructing, uniformly over ALL target geometries and masses, a coupling of the optimal plans whose total squared product-space cost is O(w). The fixed source-optimal lift need not have that cost, as the exact D_a calculation shows. Its failure is not an impossibility argument against a different coupling.

One can quantify a different obstruction in the same example without mistaking (b) for (c). On the product square x {+/-e1}, F(z,t)=z2 t1 is sqrt(2)-Lipschitz. Its expectation changes by

Delta_a = (epsilon a/2) integral y k(y)dy + E[epsilon a^2 h(X1/a)k'(X2) sign(S_a,1(X))].

The last term is bounded in absolute value by
(epsilon a^3/4)(integral |h|)(integral |k'|).
Therefore Delta_a >= c a for small a, and Kantorovich--Rubinstein plus W1<=W2 gives graph-plan distance >=c' a. As w_a is comparable with a^(3/2), this rules out uniform source-only graph-plan exponents ABOVE 2/3 for this example. It neither proves a 2/3 upper bound nor rules out the prospective square-root estimate. Thus the actual work leaves an upper 1/3 estimate and an obstruction only above 2/3; the relevant metric gap is explicit.

Attempted direct reduction: disintegrate the two plans over the SAME target and couple their conditional source laws. This is feasible and gives a target-preserving graph coupling, but no estimate uniform in arbitrarily small target masses and degenerating cells has been derived. The optimal source coupling need not preserve target labels, whereas the target-preserving conditional coupling need not retain its small source cost. Replacing one by the other is precisely the unpaid estimate. Naive independent conditional couplings can have order-one cost even as w tends to zero and so are not a solution. Classical conditioning, the convex oscillation bound and Source374 alone give the upper bound above, not the improved coupling cost.

No full result with that additional operation is closed. This exploratory objective has NOT been frozen as a theorem or restated as a finding. The common-source density-robust Q, old LC and all other completed/frozen scopes remain unchanged; this packet offers none of them for a new grade.
