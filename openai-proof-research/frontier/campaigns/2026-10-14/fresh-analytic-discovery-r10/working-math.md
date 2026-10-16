# Mathematical checkpoints after the P freeze

These are research deductions/supporting lemmas, not replacements for P.

1. Local leakage obstruction. If an everywhere-positive marginal has central
density f and the four branch pullback densities b_j satisfy b_j<f on a
compact central set Q, a preserving map cannot equal H_j on any positive
measure subset of Q. If every optimal triple contained in the five source
components has the old finite contact form, an optimal Monge pair would
have to send at least one of its two outputs outside those components on
almost every Q. Hence mu(Q)<=2 mu(U^c). Small Gaussian admixture violates
that bound while retaining b_j<f on Q. The missing hypothesis is exact
optimal-contact localization for the P marginal, not Gaussian smoothness.

2. Constant extension is admissible but cannot calibrate positive exterior
mass. Set w=u on the source union U and w=-2M off U, M>=sup_U|u|>0.
Any triple meeting U^c has sum w<=0 and strictly positive Coulomb cost.
A finite optimizer of a marginal charging U^c cannot saturate w.

3. Symmetric c-transform alone is unsafe. For w=-a<0 on all R^3,
Tw(x)=inf_{y,z}(c(x,y,z)-w(y)-w(z))=2a, whose threefold sum is not
admissible. This is an exact Coulomb obstruction, not a finite diagnostic.

4. Averaged c-transform repair. Given bounded globally admissible w and
fixed equality triples, iterate w_(n+1)=(2w_n+Tw_n)/3. Summing the three
one-coordinate transform inequalities proves admissibility. Values rise;
existing equality triples pin every coordinate in their projections.
For the source, the four outer centers stay at zero, and choosing the
opposite-sign e1,e2 centers gives Tw_n<=2+1/sqrt(2) globally. Thus the
iteration has a bounded monotone limit w_infty=Tw_infty preserving all
old contact sheets. Near-minimizers stay a uniform distance from collisions,
so Tw_n have a common global Lipschitz constant; w_infty is Lipschitz.
The limit-inf interchange uses monotonicity, not compactness.

5. Infinity and the remaining contact defect. Put
 a=inf_(y!=z)(|y-z|^-1-w_infty(y)-w_infty(z)).
Then w_infty(x)>=a and w_infty(x)->a at infinity, by a fixed-pair upper
test and the nonnegative two remaining Coulomb terms. Source values imply
a<=-3/2; max w_infty<=2+1/sqrt(2)<3. Both partners cannot escape in a
minimizing sequence for Tw_infty(x). If exactly one partner escapes,
the surviving pair (x,z) must attain a. This bad-pair projection is compact:
for x large, w_infty(x) near a; for z in a fixed compact set use
|x-z|^-1-w_infty(x)-w_infty(z)>=-w_infty(x)-max w_infty,
and for z outside use the tail limit. Both bounds exceed a because
2a+max w_infty<0. Thus all sufficiently far points have finite contacts.
This does not prove contact projection on the compact remainder, or smooth
positive marginals after projecting a contact-supported measure.

6. Two attempted completions remain unpaid. A free-reservoir primal completion
can create singular incoming marginals in the five components; existence of
contacts or measurable selections does not bound these densities. Weak limits
of graph couplings can be nongraphs, so convergence of optimizers to the source
counterexample cannot refute a deterministic optimizer after filling gaps.
No proof of P or counterexample to P is obtained.
