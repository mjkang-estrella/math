# A dominated coupling for finite-half-plane graph limits

Live author argument. This targets the DH reference-family obstruction; it
is not a complete proof of the original full no-bigeodesics target. The
pre-coalescence directional properties of the DH limiting graph are an
explicit premise below until their operative proof interfaces are checked.

## Lift and dominate the approximating laws

Write X=(t,U) for the underlying product field, and let Phi_alpha(X) be the
out-degree-one graph of unique s-geodesics to the half-plane H_alpha. Include
X itself when averaging these graph laws over alpha in [0,n]. Passing to a
subsequence yields a lifted limiting law nu on (X,graph); the original marginal
of X is unchanged. One can retain Busemann coordinates as in DH if needed.

Fix a finite original-edge set F and a finite a with r=P(t>a)>0. Independently
resample t on F from G conditioned on t>a, leave the rest of X fixed, and call
this X'. Recompute Phi_alpha(X') for the SAME alpha. The modified X marginal
has density r^(-|F|) 1{all t'_F>a} with respect to the underlying iid law.
Thus its graph pushforward, including X', is bounded above by C=r^(-|F|)
times the unmodified graph pushforward, uniformly in alpha and n.
Take a joint subsequential limit of the old/new pairs along the same
subsequence defining nu. Its old marginal is nu and its new marginal nu'
satisfies nu'<=C nu. This follows first by integrating bounded nonnegative
continuous functions, and then by regularity of probability measures on the
countable product Polish space. No finite-energy property of the cap field
is used. On the event max_{e in F}t_e<=a the original modification is upward.

The cap map is continuous at almost every underlying field: every finite
list of L_e is determined by finitely many open indicators (a shortest
circuit exists, and only finitely many circuits can be shorter), none of
whose weights equals M. Its continuous original/auxiliary values then
produce continuous capped values. The same holds for the absolutely
continuous modified marginal. One can therefore include cap coordinates
in the joint limit without changing their defining relation.

## Stability of an uncapped limiting ray

Claim: on max_F t<=a, if a ray of the old limiting graph from a fixed root v
is uncapped throughout and avoids F, the new limiting graph has exactly the
same ray from v, almost surely under this coupled limiting law.

Here are the needed tight localization facts, rather than an assumption that
arbitrary geometric geodesics are automatically selected after modification.
First, the support of the cap change is finite almost surely, and its radius
is tight uniformly over the approximating laws. The old/new underlying joint
law is the same for every alpha and n. The finite-influence argument in
tail-and-modification.md applies to its iid/absolutely-continuous marginals.
Thus for any epsilon>0 choose R so that the probability of a cap change
outside [-R,R]^2 is at most epsilon (also include v and F in this box).

Second, for this fixed R, choose S so that with probability at least1-epsilon
no old finite geodesic between two vertices in [-R,R]^2 leaves [-S,S]^2.
Such S exists because the almost-sure cheap-long-path exclusion gives a
finite bound on the length of every such geodesic, simultaneously for the
finitely many endpoint pairs. This event depends only on the old metric,
whose marginal is fixed uniformly in alpha. Therefore any old finite
half-plane geodesic from v, once it leaves [-S,S]^2, never returns to the
possible cap-change region [-R,R]^2.

In a Skorokhod realization of the coupled subsequential convergence, finite
initial graph paths converge edge by edge. On the asserted uncapped limiting
ray, every edge satisfies t_e<K_e strictly almost surely: equality has
probability zero conditional on the status field, by continuous t_e and U_e.
For a fixed prefix to the first exit from [-S,S]^2, this strict inequality
and avoidance of F persist in the old approximants. On the upward event,
all these prefix edges are unchanged in the new cap field. On the two good
localization events, every later edge of the finite approximating path is
outside the changed region, hence unchanged too. The entire finite
point-to-half-plane path is preserved by monotonicity; uniqueness means
that it is exactly the recomputed new path. Its finite graph prefix therefore
agrees with the old prefix in the limit. The exceptional probability is at
most2epsilon, plus vanishing errors from the finite-prefix convergence.
Let epsilon decrease to zero and then take a countable union over desired
prefix lengths and roots. This proves the claim.

Equivalently, the claim can be phrased with closed finite-prefix events and
small threshold margins to avoid any reliance on convergence of indicators
of non-cylinder events. The strict uncapping margins and the tight no-return
bounds are the two points that make that approximation legitimate.

## Conditional coalescence consequence for the limiting graph

Assume the lifted old limiting law is translation invariant, its paths are
unique geodesics, intersecting paths merge, and on the event of noncoalescence
there is a positive-probability triple of disjoint paths eventually moving
into all translates of one of the eight half-planes. These are precisely
pre-coalescence inputs to be supplied from the DH construction, not assumed
from the cap law's nonexistent A2(v).

Cut three such paths at last contacts with a far common lattice level after
their finitely many capped edges. By countable selection and translation
invariance there is a deterministic positive-probability event of three
entirely uncapped disjoint rays, strictly on the positive side after their
roots. Choose a sufficiently long incoming wall F around the root interval
and an enclosing cheap M-open circuit as in cubic-wall.md. Its success
probability tends to one, so the intersection still has positive probability.
Then choose a large enough finite a>=H_wall so that max_F t<=a retains
positive probability. Perform the fixed resampling just described.

The stability claim preserves all three as rays of the NEW limiting graph.
Cubic wall costs and the cheap unchanged enclosing circuit imply that its
middle class has a least element, including any finite exceptional roots
inside the circuit. The new law is dominated by C nu, whereas mass transport
under the translation-invariant old nu says that no class has a least
element almost surely. This is a contradiction. Therefore the stated
pre-coalescence inputs imply coalescence, using original iid resampling.

Unlike the earlier selector-conditional wall note, this consequence needs
no AH9.5 selector stability: it obtains stability for the particular finite
half-plane graph limits from uniqueness and tight finite influence. It still
needs the actual DH tightness/direction/merge inputs, and subsequently AH's
extraction/label machinery and the pinned source212's final iid arguments.
No completed full theorem, independent validation, or nomination is claimed.

## Operative pre-coalescence inputs and target convention, now read

DH1209.3036v1 A2 at extracted145–180 requires exactly translation ergodicity,
square symmetries, a (2+epsilon)-moment, and bounded limit shape; A2' adds
unique passage times. The cubic cap has these properties: conditional on the
entire open-status field, the original magnitudes remain independent nonatomic
conditional variables, auxiliaries are independent continuous variables, and
K_e is a fixed-length function of its own auxiliary. Thus capped edge weights
are conditionally independent and nonatomic. Any two distinct simple finite
paths have unequal sums almost surely, by conditioning on an edge appearing
in only one of them. Countability gives unique finite passage times. The
moments and norm shape were supplied in the preceding notes.

DH557–745 gives the averaging/tightness/invariance construction, and1190–1333
contains full Proposition5.1/5.2 and Theorem5.3 proofs. These are under A2',
without upward finite energy; that hypothesis enters at Section6. Directed
paths are geodesics, have out-degree one and merge on intersection, and their
directions lie in the supporting arc determined by the limiting cocycle.
DH6.2 (read1330–1455) places this arc strictly inside one of eight half-planes
and extracts a triple on a positive-probability noncoalescence event, using
stationarity rather than an unjustified ergodicity of the enlarged measure.
Thus these pre-coalescence statements apply to the cap law at their stated
hypotheses. This is use of the primary results, not a claim of independently
reproving all their preceding proofs. The dominated coupling replaces their
Section6 upward-finite-energy step.

DH's exact target is a Euclidean LINE L_alpha, rounded to the lattice set
hat L_alpha={z:(z+[-1/2,1/2)^2) intersects L_alpha}; see actual-read295–325.
The coupled proof above works with precisely this line-target graph as well:
all references to half-plane approximants can be replaced by these DH line
approximants. The uniform uncapping lemma remains true. If a target vertex
is strictly inside a lattice circuit, its half-open unit square is contained
in the polygon's interior, since the circuit has axis-aligned integer edges.
The target line thus crosses that interior and subsequently its boundary.
At a boundary crossing on a lattice edge, the nearest-cell convention rounds
to one of the edge's two vertices (with the prescribed half-open tie choice).
That boundary vertex belongs to hat L_alpha. The same cheaper boundary arc
therefore reaches a valid target. Boundary targets and paths exiting the
circuit are already covered by the previous replacement proof.

No identification of line and half-plane graph laws is asserted or needed:
use DH's exact line convention throughout this application. The primary
pre-coalescence premises above are now supported by actual statement/body
reads. What remains unreviewed is the new dominated-coupling argument and its
full integration with AH labels and the source212 proof, not a supposed
automatic restoration of finite energy. The original full theorem is still
unfinished and un-nominated.

## Reference families and upward original modifications: a further route

Choose a differentiability point of the deterministic cap norm ball and its
unique supporting functional rho. DH Corollary4.7 (actual-read) makes the
limiting cocycle slope deterministic rho. If the new coalescence proof above
is completed, the AH5.4–5.6 conditional-quantile construction (actual-read)
extracts, for almost every deterministic quantile, a measurable coalescing
family with this slope. The fixed-functional comparison AH4.4 then identifies
all such families. Here that comparison is valid for the cap's integrable
restricted boundary metric; alternatively the pinned source212 Appendix9,
now actually read completely, supplies its stationary-correction proof.
Its use of iid boundary ergodicity is supplied for the cap by its factor-iid
mixing. This does not import the original heavy-tail shape theorem.

As a result the conditional limiting graph law given the cap field is a
point mass at one reference family G_rho. Indeed the quantile representation
recovers the whole conditional law, and almost all quantiles give the same
family. Thus the dominated limiting coupling has old/new graphs equal to
G_rho(s),G_rho(s') almost surely (new domination transfers this point-mass
property).

Apply the uncapped-ray stability claim to a sufficiently late vertex of any
old reference ray. Every such ray is eventually uncapped and eventually
avoids the finite original set F. On max_F t<=a, its selected suffix therefore
coincides in old and new graphs. This proves reference-family tail stability
under the required ORIGINAL upward resampling, without needing to assume
AH9.6 for an arbitrary cap resampling coupling. A countable union over roots
and a finite collection of rotated reference functionals gives simultaneous
reference stability. Choose all four reference families by square rotations
of this differentiability-point construction.

AH9.7 can then use the previously derived uniform cap metric/Busemann
estimates to obtain cones where these reference rays avoid the finite cap
change and agree in both fields. This is a concrete way around the apparent
need to restore a general cap conditional-resampling property. The remaining
AH9.8 local-prediction and extremal-label steps must still be written and
checked under this original-field coupling; the entire AH/source transfer
is not asserted completed here.

## Localization probability bookkeeping

For clarity, the stability proof does not require the two good localization
events to occur eventually along every Skorokhod sample. Fix a desired finite
ray prefix and epsilon>0, and choose R,S as above. On the limiting event
that the old ray is entirely uncapped, avoids F, and old max_F t<a (equality
has probability zero), strict uncapping and finite graph convergence ensure
that the prefix up to the first exit from the S-box is unchanged in all
sufficiently late approximants. If the limiting old/new desired prefixes
differ, finite graph convergence makes those prefixes differ eventually too.
Therefore, on this limiting bad event, at least one localization failure
must occur in every sufficiently late approximant. Fatou gives probability
at most liminf P(localization failure)<=2epsilon. Let epsilon tend to zero.
This supplies the required limit passage even though no almost-sure eventual
localization bound was asserted under the chosen Skorokhod realization.
