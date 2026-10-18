# Analytic r44 — active T221R derivation

Author: Myeongjin Kang; original prose CC BY 4.0. No nominee yet.
Pinned source truths are assumed, not audited. Prior packets stay immutable.

The 349 screen is saved separately. The current target is fixed in
original-scope.txt. This is not a Levy-tail continuation: r32's family-221
entry was only an abstract-level Levy-spin lead. The actual source
introduction explicitly separates its Poisson hierarchy formula from the
regular-graph invariant-kernel formula of Coja-Oghlan–Perkins and the
regular hierarchy upper bounds. That is the operation-level distinction
being tested, not a novelty conclusion from absent search hits.

Actual primary reads so far: COP arXiv1808.03440v1 extracted 170–284,
550–676, 2370–2547; Lelarge–Oulamara arXiv1708.02457v2 1–235, 476–577,
1350–1573; Concetti arXiv2508.17049v1 25–185 and references 2810–2845
(initial combined output truncated part of 1–24, not credited); FLT
cond-mat/0307367v2 45–180. COP v2/v3 requests returned 404, then v1
succeeded. Whole downloaded papers are not whole-paper readings.

Lelarge–Oulamara Theorem 3 gives the required finite-hierarchy upper bound
for bounded couplings and fields, including arbitrary prescribed regular
degrees. Its recursion matches the source's independent-label power means.
Its §§5–6 explicitly describe the RSB upgrade as the existing Panchenko–
Talagrand weighting argument. COP §6 already owns the generic cavity
opening/insertion method. No claim that these are new is intended.

The possible new bridge is a large cavity pool on which the source's
hierarchical perturbations can concentrate, while the pool remains an
o(n) modification of the regular graph. Set q_n approximately n^(9/10),
rounded to an admissible even integer. Use q_n distinct vertices of degree
d-1 and all other vertices degree d. Perturb only the cavity vertices with
the source's Poisson factors, total mean s_n=n^(3/4). The needed ordering is

    sqrt(n) << s_n << q_n << n.

The source's averaged score proof needs root-log variance O(n), which
matching exposure with bounded switch costs should provide, not iid edges.
Its Palm/colored-tree identities and entire decorrelation induction then
apply with the observed-coordinate average over q_n cavity spins. This
must be stated and proved as a replacement interface; the source theorem
for Poisson graphs cannot just be invoked for regular graphs.

For a two-vertex increment, start with q_n+2d cavity vertices. Complete it
either by d bonds between 2d selected holes or by two new d-stars. Filling
holes changes the localized perturbations by expected O(s_n/q_n). The
star side has O(q_n/n) exceptional neighbor probability, for which bounded
switch coupling is needed (probability alone cannot multiply an O(n)
log partition function). The bond side is tilted by the number M_d of
d-edge matchings on full-degree vertices. A possible quantitative route:

    M_d = E_ff^d/d! + O_d(n^(d-1)),
    E_ff = deterministic(n,q_n,d) + E_hh,
    Var(E_hh)=O_d(q_n).

Consequently Var(M_d)/(E M_d)^2=O_d((q_n+1)/n^2). Coupling this density
tilt with root-log variance O(n) costs O_d(sqrt(q_n/n))=o(1), rather than
the incorrect O(n) times a total-variation bound. Counts include labelled
configuration edges and exclude loops/shared endpoints in M_d. The exact
enumeration and conditional law still need a full proof.

Jumps of q_n are sparse and have bounded increment cost. A telescoping
argument can select low increments at the remaining sizes; one must check
all parity classes and retain the original all-size liminf. At each fixed
depth choose deterministic perturbation parameters with small score errors
and low increment, then use source all-multioverlap decorrelation and
insertion comparison. Independent trial labels factor the two-star and
d-bond products through every conditional power mean, producing precisely
two times the target functional. Only after the size limit is depth sent
to infinity. The upper bound would then give convergence, with bounded
truncation paying general integrable J,H and concentration paying the
simple-graph conditioning.

Remaining work: prove the reservoir laws, switch/tilt estimates, localized
score replacement, and full limit order; inspect remaining actual primary
interpolation operations and source tree-calculus assumptions. These are
obligations, not claims of a completed theorem. No source restriction has
been silently removed and no target weakening is authorized by this note.
