# Everywhere-positive Coulomb nonattainment: second research attempt

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT.
Private third-party material retains its rights.

**UNRESOLVED FULL P.** Neither the frozen existential statement nor its
negation is proved. The original scope is unchanged byte-for-byte. No
independent proof/contribution PASS, nomination, manuscript, formalization,
publication, submission, or count increase is claimed. The campaign stays
4/10. The deductions below are technical support for this unsuccessful
attempt, not replacement results.

## 1. The unchanged target and exact remaining operation

Find a real g in S(R^3), g(x)>0 at EVERY x, with integral g^2=1. For
mu=g^2 dx and the unchanged Coulomb cost

    c(x,y,z)=1/|x-y|+1/|x-z|+1/|y-z|,

with infinite collision cost, its minimum over Pi(mu,mu,mu) must be finite
and attained, while EVERY pair of mu-preserving Borel maps has strictly
larger cost. Finite-cost preserving pairs must approach that minimum.
There are no map regularity, cyclicity, complexity, marginal approximation,
support-gap, or changed-cost qualifications. This is existential: a failed
construction below is not a counterexample to P.

The remaining operation is still an actual global construction. In the
r10 route, one needs a contact-supported probability for a bounded global
calibration preserving the source sheets, with equal everywhere-positive
Schwartz-square marginals. Section 4 proves that a global cover by smooth
contact charts, with all three projections diffeomorphic, would suffice,
including the full tail and square-root estimates. **Such a cover has not
been constructed for r10's potential or for a replacement calibration.**
Section 5 demonstrates why strict pair minimization alone cannot justify
all projection ranks. No generic smoothness of the Lipschitz fixed point
is assumed. Section 6 rules out common-translation Gaussian smoothing as
a way to preserve the source plan's optimality.

## 2. Inputs and continuity retained

All OpenAI mathematical interfaces are stipulated true at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The source family is
*A counterexample to the Monge ansatz for the three-marginal Coulomb cost*,
September 25, 2026. Its pinned prefix is

https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-counterexample-to-the-Monge-ansatz-for-the-three-marginal-Coulomb-cost-September-25-2026/build/

The actual sections read give these contracts:

* `introduction.tex`, thm:main: the smooth compactly supported example,
  excluding all preserving Borel map pairs. Its density has gaps.
* `local.tex`, lem:local: two smooth local contact branches, with both
  minimizing coordinates diffeomorphic. Invertibility is separately proved
  by a large-K argument; it is not inferred just from strict convexity.
* `certificate.tex`, prop:certificate and lem:common-ball: a central ball B,
  four branch diffeomorphisms H_j, disjoint images, and a componentwise
  smooth bounded u on V=B union_j H_j(B). Contacts in V^3 over B have
  exactly the prescribed two opposite-pair forms.
* `splitting.tex`, lem:splitting, and `proof.tex`, eq:mu and eq:optimal-value:
  mu_0=nu/3+sum_j (H_j)#nu/6, a smooth compactly supported square marginal,
  and a symmetric calibrated plan pi_0. Every point of V is a coordinate of
  an original contact.
* `infima.tex`, prop:equal-infima: equality of infima for this example;
  `riesz.tex`, thm:riesz: the already-paid all-dimension/all-exponent family.
  Neither is a new target.

The sealed r10 package was independently hash-checked before its inspected
read-only verifier was run, against external anchor
bcfbac0e38180f79dcb4461dd344ef2888291511c9de914e6a58c625226b7892.
All 100 own files, 71 pinned blobs, historical packages with 134/15/9 files,
and 17 external references authenticate. The full report, frozen scope,
working notes, source contracts, literature screen, supplied original brief,
and parent disposition/verification were read. The complete mandatory
fk-frechet-parent/fresh-r9-brief.txt, G candidate, both G reviews and parent
qualifications were read. Historical ownership instructions grant no writes.
F/G remain proof PASS / contribution TECHNICAL; the false universal tree-gap
claim remains excluded, G's distributional norm law is retained, and unread
pruning literature is not evidence. C, U, H, B, T2, EPnI, BG4, Liouville,
restricted-host mixing, Randers, and tree reconstruction remain excluded.
R and crossing work are outside this assignment. I217 remains a distinct
unfinished map-complexity problem.

## 3. What the old obstruction would give, with exact calibration

For reference this section reconstructs the reduction used here. Let Q be
compact inside a set where the central bump density nu=g_b^2 dx is positive.
Write f for a candidate marginal's density on Q and

    b_j(x)=rho(H_j(x)) |det DH_j(x)|.

If b_j<f a.e. on Q, a preserving Borel map T can equal H_j only on a null
subset of Q. Indeed for S={x in Q:T(x)=H_j(x)}, the image H_j(S) is Borel,
and preservation gives

    integral_S f = mu(S) <= mu(H_j(S)) = integral_S b_j.

Strict domination proves the claim; no derivative of T is used.

Let w be bounded and globally feasible, equal to u on V. If some finite
coupling for mu saturates w, then every optimal coupling saturates w by
integration of nonnegative slack. An optimal Monge pair would, for a.e.
x in Q, have at least one output outside V; otherwise the original
certificate and the previous argument exclude its first selected branch.
Consequently

    mu(Q) <= 2 mu(V^c).                                      (3.1)

Suppose a common-contact background sigma=h^2 dx with h>0 Schwartz were
available. Put mu_e=(1-e)mu_0+e sigma. Let

    b=nu(Q)>0, m=inf_Q g_b^2>0,
    K=max_j sup_Q h(H_j(x))^2 |det DH_j(x)|.

Then f_e-b_e,j >= (1-e)m/6-eK>0 if e<m/(m+6K). Also
mu_e(Q)>2mu_e(V^c) if e<b/(6+b), by mu_0(V)=1. The square root of its
density is smooth positive and equals sqrt(e)h outside a compact set;
hence it is Schwartz. The mixed source/background contact plan would be
finite and calibrated, so (3.1) would exclude EVERY Monge optimizer.

Finiteness and existence need no new theorem: for bounded rho,

    integral |x-y|^-1 rho(y)dy <= 2 pi ||rho||_infinity+1.

Thus the product coupling has finite cost. Fixed-marginal couplings are
tight, weak limits retain the marginals, and the nonnegative lower
semicontinuous cost gives a minimizer. Colombo--Di Marino's author-version
Theorem 1.1 and Remark 1.3 give equality with the preserving-map infimum
for nonatomic marginals. A finite infimum supplies finite-cost pairs at
arbitrarily small excess. These operations leave only nonattainment unpaid.

The r10 averaged iteration starts with u on V and a sufficiently negative
constant outside, then uses w_next=(2w+Tw)/3. The feasibility proof averages
the three inequalities c>=Tw(x)+w(y)+w(z). Monotonicity, pinning old contacts,
and the opposite-center test bound it by C=2+1/sqrt(2). The transforms have
uniformly separated near-minimizers and hence a common Lipschitz bound.
Monotone interchange of the two infima proves the fixed-point identity in
the limit. This reasoning was rechecked; it constructs a feasible
Lipschitz w, not a new marginal or an optimal potential for a prescribed
positive admixture.

For a=inf_(y!=z)(|y-z|^-1-w(y)-w(z)), one has a<=-3/2, w>=a and
w(x)->a. Since 2a+C<0, binary minimizing pairs exist in a compact set.
A minimizing sequence for Tw(x) cannot have both partners escape; a
one-partner escape makes x a coordinate of a binary minimizing pair.
Thus finite contacts are known outside that compact projection R and on V.
Neither nullity of R minus V nor global smooth contact charts follows.
These supporting facts are retained with their original limitations.

## 4. A complete gluing argument IF a global contact atlas is constructed

This section pays a conditional analytic operation, not the missing atlas.
It is not a proof or nominated contribution for P.

Assume w is a bounded Borel globally feasible potential. Suppose there is
a family of charts

    F_n=(F_n1,F_n2,F_n3): D_n -> (R^3)^3,

where D_n is open in R^3, each F_ni is a smooth diffeomorphism onto its
open image, and every F_n(t) is an exact finite contact for w. Assume the
union of all three coordinate images of these charts is ALL of R^3.
No uniform derivative, tail or distortion bound is assumed. Then there
exists a probability eta on the exact contacts of w with all three
marginals equal to h^2 dx, for an everywhere-positive Schwartz h.

### 4.1 Countable compact patches and good flat bumps

Take all parameter balls A with closure contained in a chart domain, and
on A, with center t_0 and radius r, use a normalized bump-square density

    beta(t)=Z^-1 exp(-2/(r^2-|t-t_0|^2))  for t in A,
    beta(t)=0 otherwise.

Its positive set is precisely A. Each point in any chart coordinate image
belongs to the image of such a ball. Those coordinate images form an open
cover of R^3, so the countable-basis/Lindelof property selects countably
many patches whose coordinate images still cover R^3. Explicitly, for each
rational basis ball contained in some covering image choose one such image;
the chosen images cover every point. Index the corresponding patches by n.
Their closures lie compactly inside their original domains.

For each patch, form eta_n by pushing beta_n dt through F_n and averaging
its six coordinate permutations. Its three marginals are all f_n dx, with

    f_n = (1/3) sum_i (F_ni)#(beta_n dt)/dx.

Every f_n is a nonnegative smooth compactly supported probability density,
and is positive on the union of that patch's three coordinate images.
The change-of-variables formula proves these claims: on each image its
summand is beta_n(F_ni^-1(x)) |det D F_ni^-1(x)|, extended by zero.
All relevant maps/Jacobians are smooth on a neighborhood of the compact
patch closure; the Jacobian stays positive and finite there.

For every multiindex alpha and integer m>=2 there is a finite A_n,alpha,m
such that, globally,

    |D^alpha f_n| <= A_n,alpha,m f_n^(1-1/m).                  (4.1)

To verify this, differentiation of the displayed flat exponential gives
that exponential times finitely many powers of the reciprocal boundary
distance polynomial and bounded smooth factors. Dividing by its
(1-1/m)-power leaves a positive exponential decay, which dominates every
such power at the boundary. Composition with the smooth inverse map and
multiplication by its positive smooth Jacobian preserve the estimate.
It holds outside the support by flatness. Summing three nonnegative
summands uses sum_i q_i^(1-1/m)<=3^(1/m)(sum_i q_i)^(1-1/m).
This proves (4.1), rather than assuming square-root regularity of an
arbitrary nonnegative smooth function.

### 4.2 Diagonal weights and the square-root estimate

Choose positive weights a_n so small that sum_n a_n<infinity and both

    sum_n a_n p_N,k(f_n) < infinity,                          (4.2)
    sum_n a_n A_n,alpha,m^m < infinity                       (4.3)

hold for every nonnegative integer N,k, every alpha and m>=2, where
p_N,k is the usual maximum of (1+|x|)^N |D^alpha f_n(x)| for |alpha|<=k.
There are countably many finite constants. Enumerate them, and choose

    a_n = 2^-n / (1 + maximum of the first n constants for patch n).

For any fixed constant in the enumeration all terms beyond its index
are bounded by 2^-n, and the finite initial terms are harmless. Include
1 among the constants. This is an actual simultaneous choice of weights.
Normalize the weights to sum one; (4.2)-(4.3) persist.

Set f=sum_n a_n f_n and eta=sum_n a_n eta_n. Equation (4.2) proves convergence
in every Schwartz seminorm, with termwise derivatives. Thus f is Schwartz,
nonnegative and has integral one. The cover and positive weights prove
f(x)>0 at EVERY point, with no exceptional closed set. Eta is a probability
with all three marginals f dx, and it is supported on the contacts in the
measure-theoretic sense: each summand assigns the contact complement mass
zero. The contact set is Borel because w is Borel.

Holder's inequality and (4.1),(4.3) give the essential relative bounds

    |D^alpha f|
      <= sum_n a_n^(1/m) A_n,alpha,m (a_n f_n)^(1-1/m)
      <= (sum_n a_n A_n,alpha,m^m)^(1/m) f^(1-1/m).            (4.4)

Let h=sqrt(f). Positivity makes h smooth. For |alpha|=k>=1, differentiating
sqrt(f) gives a finite sum of terms

    constant * f^(1/2-l) product_(j=1)^l D^beta_j f,
    1<=l<=k, beta_j nonzero, sum_j beta_j=alpha.

Use (4.4) with m>=4k for every factor. Each term is bounded by a constant
times f^(1/2-l/m), hence by a constant times f^(1/4), since f is bounded.
A fourth root of a nonnegative Schwartz function decays faster than every
polynomial as a function, by using the 4N-th decay bound for f. Therefore
all derivatives of h decay faster than every polynomial; h itself does
also. This proves h in S(R^3), h>0 everywhere and integral h^2=1.

Finally every eta_n saturates w, so eta does, and

    integral c deta = 3 integral w f dx < infinity.

This equality can first be summed for the nonnegative cost, and the
bounded potential justifies the marginal integrations. Integrating global
feasibility against any competitor proves optimality. This completes
the conditional gluing proof on ALL of R^3, including tails.

### 4.3 What has not been obtained

The source supplies such charts only on V. R10 supplies a bounded
Lipschitz fixed point and individual finite contacts off R, not the above
charts there. Neither smoothness of the potential, a nondegenerate local
minimizer, nor invertible coordinate derivatives at those contacts has
been established globally. Even a.e. contact projection is weaker than
the open cover used here. The gluing theorem does not assert any of these
hypotheses, and is not a proof of CP. CP could also hold without this atlas.

## 5. Strict minimizing Hessian does not give every projection rank

Here is an exact local Coulomb example explaining a remaining atlas risk.
It does NOT assert singular projected marginals for r10, and does not
refute P. Use the center (x,y,z)=(0,e_1,-e_1), and let

    H=diag(2,-1,-1),       J=H/8=diag(1/4,-1/8,-1/8).

These are the pair Coulomb Hessians at distances one and two. Define
quadratic potentials u_2 near e_1 and u_3 near -e_1 with values zero,
gradients -5e_1/4 and +5e_1/4, and Hessians

    D^2 u_2=diag(5/4,-17/8,-17/8),
    D^2 u_3=diag(5/4,-5/4,-5/4).

For F(x,y,z)=c(x,y,z)-u_2(y)-u_3(z), its (y,z)-gradient vanishes at the
center. Its pair Hessian there has blocks

    A_11=I_3, A_22=diag(1,1/8,1/8), A_12=A_21=-J.

It is positive definite: after grouping matching axes, its 2 by 2 blocks
have positive leading entries and determinants 15/16, 7/64, 7/64.
The implicit function theorem and strict convexity on sufficiently small
convex product balls give a smooth unique minimizing pair Y(x),Z(x).
Set u_1(x)=F(x,Y(x),Z(x)). Then c>=u_1+u_2+u_3 locally, with equality
precisely on that minimizing sheet. This is a genuine local calibration,
not just an arbitrary matrix test.

The mixed x derivative has both blocks -H. Differentiating the stationarity
equations gives

    (DY,DZ)^T = -A^-1 (-H,-H)^T.

Solving the three displayed 2 by 2 systems exactly yields

    DY(0)=diag(8/3,0,0),   DZ(0)=diag(8/3,-8,-8).              (5.1)

Thus one projection has rank one although the pair minimization Hessian
is strictly positive definite and both mixed Coulomb blocks are invertible.
An IFT for the entire pair alone is insufficient. Rank failure at one point
does not imply failure a.e. or a singular pushforward; no such stronger
claim is made. The source's separate large-K block-invertibility proof
avoids this example on its own patches. It has not been reproduced at
unknown contacts of the global fixed point.

## 6. Common Gaussian translation smooths the marginal but destroys optimality

This section is a construction obstruction, not a statement about the
existence of map optimizers for the smoothed marginal.

Let pi be any finite-cost probability on triples in R^3, and let kappa have
full support in R^3. Form the common-translation law pi^kappa by sampling
(a,b,d) from pi, t independently from kappa, and using

    (a+t,b+t,d+t).

Its cost equals that of pi by translation invariance. If the original
marginals agree, its new marginals are their convolutions with kappa.
Nevertheless pi^kappa is never optimal for those marginals.

Choose any collision-free point A=(a,b,d) in the support of pi; one exists
because pi is finite-cost. Every common translate A+t belongs to the
support of pi^kappa: continuity of translation and positive measure of
neighborhoods of A and t prove this. Choose a nonzero vector v perpendicular
to both a-b and a-d, possible in R^3, and compare the support points A and
A+v. Swapping their first coordinates preserves the sum of each coordinate
marginal. The old total cost is 2c(A). The swapped total cost is

    2/|b-d| + 2/sqrt(|a-b|^2+|v|^2)
              + 2/sqrt(|a-d|^2+|v|^2) < 2c(A).              (6.1)

All configurations here are collision-free, including the swapped ones.
There is a strict finite cost gain.

For completeness the support inequality gives a real competitor, without
assuming a cyclical-monotonicity theorem. Choose disjoint sufficiently
small bounded neighborhoods N_0,N_1 of the two support points, with positive
masses, such that all original/swapped configurations remain separated and
the strict gain in (6.1) holds uniformly for every pair from N_0 times N_1.
Take submeasures alpha_i of the restrictions to N_i with the same mass
m>0. For independent triples U,V with laws alpha_0/m, alpha_1/m, remove
alpha_0+alpha_1 and insert m times each of the laws

    (V_1,U_2,U_3),       (U_1,V_2,V_3).

The sum of first marginals, second marginals and third marginals is
unchanged. The new nonnegative measure is a probability with the same
marginals, finite cost, and a strict reduction m times the uniform gain.
Thus pi^kappa is not optimal.

Apply this to the source pi_0 and any centered nondegenerate isotropic
Gaussian kappa_tau, tau>0. Its common marginal density f_tau=mu_0*kappa_tau
has a positive normalized Schwartz square root. Here is an explicit check
of the square-root assertion. If mu_0 is supported in |s|<=L, then

    f_tau(x) = C exp(-|x|^2/(2 tau^2))
               integral exp(x.s/tau^2-|s|^2/(2 tau^2)) dmu_0(s)>0.

Differentiating the Gaussian under the compact integral gives
|D^alpha f_tau(x)|<=C_alpha (1+|x|)^|alpha| f_tau(x), and
f_tau(x)<=C exp(-(|x|-L)^2/(2 tau^2)). The same differentiated square-root
formula as in Section 4 bounds every derivative of sqrt(f_tau) by a
polynomial times sqrt(f_tau). Hence it is Schwartz and positive everywhere.
But the natural common-noise plan has cost E(mu_0) strictly above
E(f_tau dx), by the explicit competitor. Its old contact plan/calibration
cannot be declared optimal after this smoothing. This says nothing about
whether some other optimizer of this marginal is Monge; P is not refuted.

## 7. Further lines examined and not paid

A positive Gaussian admixture retains the old branch deficits but does not
make its minimizer saturate an extension of u. The r10 exterior constant
extension is strictly slack on every triple meeting the exterior. Averaging
repairs simultaneous-transform feasibility only. Separate far-separated
source optimizers have cheaper AAB/ABB cross couplings and cannot simply
be mixed. Weak graph limits can be nongraphs. All of these objections persist.

A reservoir optimization can force exterior coverage at the price of
uncontrolled incoming marginal mass. A measurable contact choice and
symmetrization do not remove atoms or lower-dimensional images. Imposing
density caps, entropy, or derivative penalties changes its stationarity
conditions; no argument here makes those constraints inactive while
preserving u. Such a variational prescription is not a constructed CP plan.

The possibility that R minus V is null was examined but not established.
Binary-minimum projection and self-conjugacy do not themselves provide a
measure estimate. No smoothness or nondegeneracy is asserted for minimizers
of the nonsmooth fixed point. No numerical experiment was needed or run.

## 8. Primary operation comparison and limits

The source already pays local Coulomb branch calculus and exact density
splitting. GKR's harmonic-cost Theorems 3.4/3.5 and Lemma 3.6 are the
shared-component antecedent, not a theorem for positive Coulomb marginals.
CDM Theorem 1.1/Remark 1.3 pay equality of values. GKR duality Theorem 4.2,
Theorem 5.2 and Lemma 5.3 provide duality/Lipschitz self-conjugate potentials
for a GIVEN marginal; none is an inverse contact-density construction.

A further bounded primary screen inspected Lelotte's dual-charge preprint
2208.14762v1, Theorems 1/2 and Lemma 7 with Section 4.2: it constructs and
studies dual charges for a specified density. Theorem 1 of 2210.07830v2 gives
potential asymptotics for positive densities on connected unbounded open
sets, and Theorem 3 gives one-particle dissociation. Those results constrain
possible completions; they do not produce this preserved atlas or CP.
No result from these new readings is needed as a premise in Sections 4-6.
[Dual-charge primary text](https://arxiv.org/pdf/2208.14762v1),
[asymptotics primary text](https://arxiv.org/pdf/2210.07830v2).

The flat-bump estimates, diagonal weighting, Holder inequality and
square-root differentiation in Section 4 are standard analytic operations,
proved here to make this conditional route exact. Section 5 is a local
calculus obstruction to an unjustified rank inference. Section 6 is an
exact swap improvement. None is separately nominated as substantial or
claimed new to the literature. The bounded search finds no proof of full P;
it is not a worldwide novelty or priority certificate. No claim that
full P is known open worldwide is made.

## 9. Provenance and handoff

`source-contracts.md` records this attempt's actual reading extent and labels;
authentication of unread bytes is not reading. `source-identities.json`
binds the exact pinned blobs used. `inputs-manifest.json` records local
private primary texts and exact external file references, without copying
historical trees. `external-input-baseline.json` records 279 protected
external inputs and exact membership of the four sealed packages.
`original-scope.md` is byte-identical to r10 and bound by `scope-freeze.json`.
`outputs-manifest.json` and `seal.json` bind the complete new package;
the seal is detached externally in the final handoff.

The read-only verifier checks the supplied external anchor before every
payload, exact file/directory membership, 71 inherited pinned Git blobs,
the old seals, frozen-scope identity and the unchanged-input receipt.
Wrong-anchor and unjustified-PROVED controls reject without modifying any
frozen input. These are artifact checks only. There is no mathematical
checker, simulation, Lean theorem, independent gate or count increase.

The parent alone integrates. The mathematical next operation is an actual
global contact atlas satisfying Section 4, an alternative CP construction,
or a different complete proof of the unchanged full P. All remain unpaid.
