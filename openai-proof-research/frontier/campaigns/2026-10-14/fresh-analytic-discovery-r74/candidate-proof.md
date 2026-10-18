# Moment-free absence of planar iid bigeodesics: unified author draft

Assembly began after scope-status.json, recorded at 2026-10-18 16:20:33 UTC.
Author completion was recorded at 2026-10-18 16:33:29 UTC after the elementary
core, nonergodic extension, symmetric label transfer and no-return repairs.
This is a full-scope AUTHOR PROOF CLAIM, not independent validation, acceptance,
or a literature-priority verdict. The status in checkpoint.json governs the
remaining gates. No earlier working note is
retroactively a frozen full proof. Parent author derivations are attributed
in parent-author-provenance.json; their snapshots are part of this draft.

## 1. Exact claim and source convention

For every nonatomic Borel probability G on [0,infinity), supported on finite
values, let (t_e) be iid G on the unoriented nearest-neighbor edges of Z².
The prospective conclusion is that with probability one there is no
bi-infinite simple path all of whose finite subpaths minimize t-passage cost.
The assertion ranges simultaneously over all such paths; no direction and
no moment is prescribed. A nonatomic law gives t_e>0 simultaneously a.s.
The bounded-support case follows from the stipulated source212 theorem.
Below G is unbounded. Its finite values need not have any positive moment.

Source212 means the pinned No-bigeodesics-in-planar-first-passage-percolation
manuscript at revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Its conclusions
under its stated moment assumption are stipulated; here we reuse its actual
proof operations with new interfaces. We do NOT apply its iid theorem to a
dependent field. AH means Ahlberg–Hoffman arXiv1609.02447v2; DH means
Damron–Hanson arXiv1209.3036v1. Exact receipts and actual reading limits are
separate. Original AH/DH general finite-energy hypotheses are not asserted
for the new field.

## 2. Probability space and a single choice of bands

Take M>0 sufficiently large that q=G((M,infinity))<1/1024. Let a=essinf G.
Choose a<a_o<b_o<M with G([0,a_o])>0 and G([0,b_o))<1/1024. This is possible
by nonatomicity at a. Unbounded support gives M<a_c<b_c<infinity with
G((M,a_c])>0 and G([b_c,infinity))>0. Define low/high bands

 L_o=[0,a_o], H_o=[b_o,M], L_c=(M,a_c], H_c=[b_c,infinity),
 p_as=G(L_s), p_bs=G(H_s), r_o=G([0,M]), r_c=G((M,infinity)),
 g=min(b_o-a_o,b_c-a_c)>0, p_*=min_s p_as/r_s>0.

All these masses are positive. An edge is usable when its ORIGINAL value
lies in H_o union H_c. Its bad probability epsilon<1/512 satisfies both
8 sqrt(epsilon)<1 and 6 sqrt(epsilon)<1/2. This stronger common choice removes
a harmless discrepancy between constants in the earlier lowering and final
perturbation notes. All thresholds remain fixed throughout the argument.
Take independent cap auxiliaries V_e uniform(0,1), independent of all t_e.
These are distinct from every later trigger uniform.

## 3. Cap core and its exact preservation statement

Call t_e<=M open. Let L_e be the minimum length of an open simple circuit
strictly enclosing both endpoints of e. Set

 K_e=M(L_e³+V_e),  s_e=min(t_e,K_e).

The elementary annulus/closed-dual-path count gives
P(L_e>CR²)<=C exp(-cR): failure of an open circuit in an annulus forces a
closed dual crossing of length at least cR, whose probability is bounded by
O(R) sum_{j>=cR}(3q)^j. A circuit in its outer box has O(R²) edges.
Thus all L_e exist simultaneously and have stretched-exponential tails;
K_e and s_e have every finite moment. The cap is a square-symmetric factor
of iid, mixing under every nonzero translation. Since L_e>=10, K_e>=2ML_e.
Every open edge is unchanged.

Condition on all open indicators. Original magnitudes retain independent
nonatomic conditional laws and V_e retain independent uniform laws; the
L_e are now fixed. Each s_e is nonatomic (both the original magnitude and
its independent threshold are nonatomic), and these variables are conditionally
independent. Conditioning on an edge present in only one of two distinct
simple paths proves unequal path sums. Countability gives finite uniqueness.
Existence of finite minimizers follows from the cheap-long-path bound in §4.

Choose a minimum circuit C_e measurably. Its choice affects the following
estimates only, not the cap. Put E_x={e:x strictly inside C_e}. Since
x inside C_e implies dist(x,e)<=L_e, summability of the tail gives E_x finite
simultaneously for every x. Set B(x)=sum_{e in E_x}t_e<infinity. No moment
or uniform spatial sublinearity of B is claimed.

For a t-bigeodesic gamma, any crossing segment of C_e between its outermost
contacts has t-cost at most ML_e/2. Hence gamma cannot use a changed edge
(t_e>K_e). Conversely an s-bigeodesic cannot use one: its crossing segment
would cost at least K_e while an open boundary arc costs at most ML_e/2.
To prove that every t-bigeodesic remains s-minimizing, take any finite
s-competitor between a,b on gamma and eliminate each changed-edge occurrence.
If both endpoints are outside C_e, replace its bracketed crossing by a boundary
arc. If just one is inside, replace its prefix/suffix by the gamma piece to
a boundary contact and an arc. If both are inside, replace the whole path by
gamma[a,b]. The added cost is at most ML_e, while the removed portion contains
K_e>=2ML_e. All added gamma and circuit edges are unchanged, so the count of
changed occurrences strictly decreases. The final walk has original cost at
most the competitor's s-cost; t-minimality finishes the proof. For the reverse
direction, an entirely unchanged s-bigeodesic is t-minimizing since s<=t.
Thus the TWO SETS OF GEOMETRIC BIGEODESICS ARE EXACTLY EQUAL, with equal
edge costs on them, pathwise on one event. Their Busemann functions need not
coincide between metrics.

The following endpoint and original-ray comparisons are OPTIONAL supporting
facts; they are not premises of the essential chain below. The same replacements
give 0<=T_t(x,y)-T_s(x,y)<=B(x)+B(y): eliminate changed
edges outside E_x union E_y, loop erase, then restore the remaining weights.
The ESSENTIAL rooted-cap-ray fact is simpler: every s-ray from x uses changed
edges only in E_x, by the crossing shortcut; hence every such ray is eventually
uncapped, uniformly outside E_x over rays from that fixed root. Its unchanged
tail is an original ray. Optionally, every original ray eventually leaves
the finite union of C_e and their interiors for e in E_x and then is an s-ray.
For this latter replacement, an endpoint inside a circuit must be joined to
a FORWARD contact along its ray; the earlier crossing contact supplies the
cost bound but is not used as the added path. The entire added tail is then
uncapped. For the optional one-sided correction along an original x-ray,
eliminate only changed occurrences outside E_x: added ray pieces may contain
E_x edges, so counting all changed occurrences would be incorrect. Loop erase
and restore E_x to obtain T_t(x,y)-T_s(x,y)<=B(x). These two bookkeeping repairs
were identified by the parallel parent-author assistance, not an independent
review. Only eventual uncapping and exact bigeodesic equivalence are needed
in the final contradiction.

Finite changes in originals with fixed V have finite cap influence on one
original full event, even without an absolute-continuity premise for the new
field. Open circuits surround every finite box on that event, so modified
protecting circuits still exist. For remote e, L_e<dist(e,F); the old shortest
circuit avoids F, giving L'_e<=L_e. Every new minimizing circuit then also
avoids F and was old-admissible, so equality holds. The summable tail gives
L_e/dist(e,F)->0 uniformly far from each finite F. Absolute continuity remains
necessary elsewhere to transfer the structural full-measure events. If originals increase then L'_e>=L_e and
s'_e>=s_e. An uncapped path avoiding F is exactly unchanged. These are geometric
statements, not assertions that arbitrary selectors are stable.

## 4. Metric inputs without original moments

The complete elementary proofs are in cap-author-cap-core.md and
cap-author-shape-and-length.md (credited coauthor snapshots), together with
the explicit fixed-event extension in cap-shape-interface.md. All three
assistance files were read in full and their endpoint/localization repairs
are incorporated above. The following sharpened observation is useful. Search
circuits of length<=R locally and put L_e^R=R if none exists. Then
s_e^R=min(t_e,M((L_e^R)³+V_e))<=s_e everywhere, agrees if L_e<=R, is bounded
by M(R³+1), and has uniformly bounded expectation. It depends only on radius
O(R) input. Splitting any coordinate segment into O(R) independent residue
classes and applying Hoeffding gives, for length ell>=eta n, failure bound
O(R) exp(-c_eta n/R^7). With R=ceil(log(n+2)^4), a union over O(n³) segments
and O(n²) coupling errors is summable. Extending short segments and using
positivity gives, for every eta>0, a.s. eventually uniformly in the n-box,

 T_s(x,y)<=C(|x-y|_1+eta n).

Choose d>0 with P(t_e<d) sufficiently small and d<M. Since s_e>=min(t_e,M),
iid simple-path counting excludes long paths of average cost<d/2, uniformly
from O(n²) box vertices with exponentially high probability. Coordinate routes
then bound all box-to-box minimizing path lengths by Ln with probability
approaching one. This proves finite minimizer existence and coercivity too.

Kingman's theorem, mixing of each directional shift and integrability give
radial deterministic limits. The local continuity estimate and rational nets
give a deterministic nondegenerate square-symmetric norm mu and uniform shape.
The fixed-event good-center argument in cap-shape-interface.md gives the
extended shifted version: for every eta>0, a.s. for sufficiently large radius,
|T_s(x,y)-mu(y-x)|<=eta max(|x|,|y|) for all relevant distant pairs, with a
finite additive constant covering the rest. Integrable stationary additive
Busemann fields of a coalescing measurable family satisfy radial linearity;
the same local continuity and good-center argument give uniform and extended
linearity. This paragraph concerns ONLY the cap metric and its Busemann fields.

## 5. Structural construction and replacement of its energy steps

This is the critical new structural chain. structural-author-bridges.md
contains the completed coauthor derivations of the new coupling/reference/
selector steps; it was read in full and its fixes are incorporated. The
remaining AH6–8 and extension premises are supplied below, so the module
is not applied outside its explicit hypotheses. The detailed proof modules are
listed here in dependency order. Each replacement is proved in the cited
module; the chain is not inferred from the original AH theorem label.

(a) Apply DH's averaging and pre-coalescence results under A2': the cap has
translation ergodicity, square symmetries, a 2+epsilon moment, bounded norm
shape and unique finite paths. Use DH's EXACT rounded-line targets, not an
identification with half-plane graph laws. The limiting graph has outdegree
one, merging paths on intersection, geodesicity and its supporting-arc
direction property. On noncoalescence DH6.2 extracts a triple in one of eight
eventual half-planes. These steps precede DH's finite-energy use.

(b) Replace that use by dh-limiting-coupling.md. Lift the old finite-line
averages to (t,V,graph), resample a fixed finite original set F from G|>a,
and recompute the SAME line graph. New marginal measures are bounded by
G((a,infinity))^{-|F|} times the old ones; this domination survives a joint
subsequential limit. On old max_F t<a the change is upward. Finite cap influence
has a tight radius uniformly in the approximation. Coercivity gives a tight
no-return box for geodesics between vertices in that radius. Finite prefix
convergence, strict uncapping margins t_e<K_e, and those two localization
events preserve an entirely uncapped limiting ray avoiding F AS THE SELECTED
new limiting ray. The exceptional limiting probability is <=2epsilon by
Fatou; letting epsilon->0 avoids any false almost-sure eventual localization.

(c) The cubic-wall proof in cubic-wall.md contradicts noncoalescence in this
dominated new graph law. Cut the triple at last contacts after uncapping.
Coordinate incoming walls of length m force L'_e>=2m, hence cap cost>=8Mm³;
raise originals above 4Mm³. A surrounding unchanged open circuit of O(m²)
edges exists with probability tending one and supplies a cheaper bypass.
For diagonal h=x+y, u=x-y, raise both edges into (k,-k), |k|<=m, from h=-1.
Their h=-1/2 crossing values are consecutive u half-integers from
-2m-1/2 to 2m+1/2; a protecting circuit has u-span>4m and L'>=4m. This pays
the same outer bypass. The middle class is confined to the corridor plus
a finite set and has a lexicographically least vertex (h,u in the diagonal
case). Stationary mass transport forbids such a class in the old law and
therefore in its dominated new law. Together with the limiting stability proof in (b), this proves
reference-graph coalescence at the author level.

(d) At a norm-ball differentiability point, DH's limiting slope is its unique
tangent functional rho. AH5's conditional quantiles extract measurable
coalescing families; AH4.4 fixed-functional uniqueness identifies them.
Consequently the conditional graph law is a point mass at G_rho(s).
Domination transfers this fact to the modified graph. Applying (b) to late
uncapped suffixes yields reference-family tail stability under the required
finite original upward modification. Four rotations supply reference families.

(e) AH6–8 order, auxiliary Voronoi flow, and label construction use these
references, shape, finite uniqueness, stationarity and independent AUXILIARY
product structure. The actual proof-dependency map is ah-6-8-integration.md.
The only downward probabilistic use, AH8.6, is replaced in full by
same-status-lowering.md. Resample a single original within its M-status and
freeze V; every L is fixed and ONLY that cap edge changes. On a usable
uncapped ray edge a decrement>g/2 occurs with probability>=p_*. Reversibility
holds conditional on the finite ORIGINAL-coordinate sigma-field. All fixed-root
rays are uncapped outside finite E_x; iid path counting supplies gamma n usable
annular edges; the length bound gives at most 3Ln edges for the reverse count.
The resulting conditional inequality is

 P(A|F_n)<=P(C1^c|F_n)+P(C2^c|F_n)+(3L/(p_* gamma))P(A^c|F_n).

Here C1,C2 have probabilities tending one, and A is AH's fixed finite-witness
bad event. Martingale convergence excludes P(A)>0. The deterministic exact
one-edge arguments AH8.4–8.5 apply because all other cap weights are unchanged.

(f) AH9.2's eventual half-plane argument uses integrable increment extensions
and shape, not finite energy. The extension need NOT inherit cap mixing.
stationary-extension-cocycle.md proves the required uniform linearity with a
possibly random globally invariant slope: two-sided axis Birkhoff limits,
fixed-displacement tail summability for global invariance, conditional bad-site
densities for fixed events, and a two-good-center axis route. All quantifiers
and the nonergodic-component choice are explicit there. To replace AH9.5–9.10, reference stability from
(d) and AH9.7's geometric proof supply unaffected cones. The common-prediction
site argument in label-stability-interface.md works for the nonstationary
coupling: each absolutely continuous marginal inherits the stationary
almost-sure density of bad local predictors; their union has density<=2eta,
less than the unaffected cone density. A site good in both fields has the
same finite patch and hence identical predicted and actual selector stubs.
AH9.8's planar comparison is applied in BOTH orientations of the pair;
its hypotheses after reference coalescence are symmetric. Every ray has a
common geodesic tail under finite cap changes by the explicit cost-barrier
lemma in label-stability-interface.md (no reattachment assertion). Monotone squeezing
between the two preserved extremals transfers every ray of the fixed label,
not only the two selectors. The reverse-label fact and AH9.9's extremal limit,
with a fixed no-return box for convergent finite minimizers, then preserve
the entire extremal selector under our original upward resampling. These
explicit steps appear in label-stability-interface.md. Isolated alpha use
an immediate predecessor/successor and the closed realized-label set;
nonisolated alpha use countable approaching sequences, as detailed there. Apply the same cubic wall to
these selectors. AH9.11 mass transport gives their coalescence.

(g) The actual proof-dependency map ah-9-10-integration.md now applies AH10's
crossing/order, compact limits and countable functional nets. It supplies a
deterministic closed slope set C, simultaneous linear cap-Busemann asymptotes
for EVERY ray, uniform all-ray cone control, and each FIXED slope's unique
coalescing backwards-finite family. No uncountable intersection of fixed-slope
null events is taken. All metric and Busemann estimates are in s.

## 6. Opposite exceptional labels via independent underlying pasting

The full parent author derivation is parent-author-halfplane-transfer.md.
Source03 lines47–48 and98–109 restrict its charts to rotations/reflections
preserving the square lattice. These are D4 isometries: coordinate Lipschitz
constants are one for Euclidean and lattice norms, and nearest-neighbor height
steps and all source07 edge-height counts are unchanged. No rational or
45-degree coordinate change is used in source04–08. The diagonal (h,u) wall
in §5(c) is a separate explicit AH/DH construction, not a source chart.
It replaces source04's iid metric splice by an independent splice of BOTH
original t and cap V. For fixed n the upper/lower outputs are independent,
each with the original cap law. Changed cap vertices lie in a sublinear
thickening of the original boundary: for the upper splice,

 z_2<=-n+3+max_{e incident z}(L_e(X)+L_e(X_n)).

The envelopes A_n(X)=sup_e L_e/(|e|+n) tend to zero a.s.; same-marginal
A_n(X_n) tends to zero in probability. Jointly diagonalize these with the
extended metric errors. For n_k, the changed vertices satisfy
z_2<=-n_k+epsilon_k(|z|+n_k), epsilon_k->0. The supporting-functional gap
on a thick lower semicircle gives for bounded x and all changed vertices z

 min(T_X,T_Xn)(x,z)-B_p^X(x,z)>=c n_k.

For fixed n and upper-sector x it gives >=c_n(|x|+|z|) for distant x.
In both comparisons the suffix after the LAST changed vertex has exactly
shared costs. Hence upper witnesses and their Busemann functions transfer;
two independent upper-sector directions identify the same linear label.
The lower construction is reflected. The detailed constants, diagonalization,
last-vertex comparison and fixed/moving quantifiers are in the cited snapshot.
Source04's independent-exceptional-set argument now gives simultaneous opposite
exceptional coalescence. This does not assert linearity of original t-Busemann
functions, or full equality of original and capped rooted ray families.

## 7. Budget, forks and arbitrary tolls

The exact new probability kernels and their derivations are in the credited
parent-author-status-preserving-perturbations.md, now checked against actual
source05–08. Here every environment event is measured on the underlying
originals plus V, with cap labels and cap distances.

One-edge resampling within its status preserves the product original law and
changes only one cap edge. Conditional on the entire output, the hidden old
value lies in its status low band with probability p_as/r_s>=p_*.
An output bigeodesic is wholly uncapped by §3. Thus a usable marked edge gains
at least g in the cap. Source05's exact geometric comparison, including base
comparator regularity at BOTH endpoints, yields

 P(A_e^{alpha,beta}(H))<=ell(H)(r(beta)-r(alpha))/(g p_*),
 E N_e(H)<=C(H+1), ell(H)<=C_0(H+1).

Usable-edge path counting is in the ORIGINAL iid field. Its simultaneous
pathwise bound applies to cap bigeodesics, whose weights are unchanged.
Source06's finite rooted-tree leaf count credits >=n F_n/4 distinct usable
edge-label pairs; uniform all-ray cap confinement bounds their expectation.
First n->infinity at fixed epsilon, then epsilon->0, excludes forks.
Opposite exceptional coalescence from §6 then identifies both cap-Busemann
functions for any two bigeodesics with the same random label, simultaneously.

For a finite deterministic source tilt region A_k(R), use independent trigger
uniforms Q_e, and samples Z_es~G|H_s. An original in L_s is replaced by Z_es
with probability delta_h/p_as, where delta_h=eta/((h+2)log(h+2)) and
eta is small enough that delta_0<=min_s p_as/2. Use the SAME one replacement
at overlapping regions. All statuses and V stay fixed, so all K_e stay fixed
and cap changes are confined EXACTLY to the designated raised edges.
The original-output density and second moment are

 lambda_h=1+sum_s[-delta_h/p_as 1_Ls+delta_h/p_bs 1_Hs],
 integral lambda_h² dG=1+delta_h² sum_s(1/p_as+1/p_bs).

There is mass delta_h moved in EACH status, total 2delta_h. The finite products
have uniformly bounded L² norm because the number of edges at height h is
O(h+H_0+1) and sum_h(h+H_0+1)delta_h²<infinity. Choose eta so output total
variation from the base is <=p/8, independently of R. Cap pushforward cannot
increase total variation. All individual/union full events transfer by
absolute continuity, over a countable collection.

Conditional on ENTIRE original output Y and all V, hidden raise indicators
are independent with probabilities

 theta_e=sum_s 1_Hs(Y_e) delta_h/(p_bs+delta_h).

A cap-bigeodesic selector is a function of (Y,V) alone. On every successful
raise along its usable prefix, Y_e=s_e<=K_e and old t_e<=a_s<b_s<=Y_e,
so old cap also equals old t_e and cap gain>=g. The output usable-prefix
condition has at least half usable edges for every prefix length>=n_0.
Abel summation gives divergent conditional expected successes, bounded below
by a positive constant times sum_{j=n_0}^R1/((j+2)log(j+2)); variance<=mean.
Choose a near radius R_0 once with mean>=8. For any toll m choose R(m) with
mean>=max(2 ceil(m/g),32). Conditional probability of a near strict raise
AND gain>=m is at least3/4. Marking probability is >=p/4. The grid spacing
ell>R_0+1+(R_0+H_0)/slope is fixed independently of m.

The shared union changes none of the edges of either selected bigeodesic:
all its low-height edges are already in its individual region; other heights
are unchanged. Competitors only increase. A near raised edge at the other
site lies outside the first region and has its BASE CAP cost there. Equality
of Busemann pairs for equal labels, followed by the source07 vanishing-excess
detour across that strict edge, forbids repeated marked labels.

Impose the source08 base comparator filter, losing at most p/8, so q_m>=p/8.
For fixed m the comparison separation S(m) is finite. Refine the finite label
partition and discard marks with same-bin neighbors within S(m). Distinct
labels and finitely many neighbors make this filter disappear pointwise as
the partition refines. The geometric label budget telescopes cap-Busemann
increments and gives q_{m,j}<=ell W_I/m; bounded convergence gives

 p/8<=q_m<=ell W_I/m.

Since p,ell,W_I were fixed before m, this is impossible for large integer m.
Every selector, radius, site, union and partition endpoint used above belongs
to a countable collection; random-label equalities are pathwise. The structural
bridges in §5 and the pasting proof in §6 supply the required premises. Hence
there are no capped bigeodesics on one event. Exact equivalence in §3 yields
the full prospective original-law conclusion, without a weakened target.

## 8. Author completion and remaining independent gates

The full original target is now claimed proved by the authors through the
ordered chain above. The elementary author assistance was read in full; its
endpoint, local-cap, finite-influence and fixed-event shape repairs are
incorporated. The nonergodic-extension lemma and symmetric label/squeeze step
are explicit, as is the no-return justification for selected-ray stability.
No currently identified technical gap remains in this author claim.

Earlier working notes and exact parent snapshots retain their original
conditional wording as a chronological record. This unified proof and the
completion record resolve those earlier author obligations; they do not
backdate completion or transform author collaboration into review.

Independent full-scope proof and contribution reviews remain pending. No
numerical checker can certify the infinite-volume structural bridges. There
is no formalization, manuscript gate, release gate, acceptance, publication,
or count change in this packet. A reviewer can reject any proposed bridge;
the author completion claim is not an independent proof verdict.
