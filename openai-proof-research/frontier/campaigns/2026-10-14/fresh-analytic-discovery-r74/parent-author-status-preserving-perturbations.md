# Conditional transfer of the budget, forks, and divergent-gain argument

Parent author derivation, 2026-10-18. Full source212 sections05-budget
(423 lines),06-forks(218),07-tilts(507),08-conclusion(140) were read. This note
credits their budget, tree counting, shared perturbation, posterior-selection,
union, and final-filter arguments as antecedents. The new interface is a
status-preserving replacement of their iid perturbation: protecting circuits
stay fixed, and cap changes are confined to exactly the edges being resampled.
It is conditional on the unfinished all-ray cap structure and the conditional
opposite-exceptional-coalescence argument in halfplane-transfer.md. No full
candidate, independent validation, or acceptance is asserted.

## Four bands and the usable-path estimate

The original law G is nonatomic on finite nonnegative values. Bounded support
is already covered by the stipulated source theorem, so consider unbounded
support. Choose the cap threshold M large enough for the earlier circuit
estimates and also G((M,infinity))<1/256. Let a be the bottom of its support.
Choose a<a_o<b_o<M with G([0,a_o])>0 and G([0,b_o))<1/256. Unbounded support
allows finite M<a_c<b_c with G((M,a_c])>0 and G([b_c,infinity))>0. Set

    L_o=[0,a_o],       H_o=[b_o,M],
    L_c=(M,a_c],       H_c=[b_c,infinity),
    p_{a,s}=G(L_s),    p_{b,s}=G(H_s),       s in {o,c},
    r_o=G([0,M]),      r_c=G((M,infinity)),
    g=min(b_o-a_o,b_c-a_c)>0.

All four p's and both r's are positive. The two statuses are whether t<=M
or t>M. Each low/high pair belongs to the same status. Call an original edge
usable if t belongs to H_o union H_c. Its failure probability satisfies

    q <= G([0,b_o))+G((M,infinity)) < 1/128 < 1/64.

The source's simple-path count (at most4^j paths, at most2^j bad-edge subsets)
therefore gives exactly its geometric tail with theta=8 sqrt(q)<1. It is an
estimate in the original independent field; cap edges need not be independent.
Every capped bigeodesic is wholly uncapped by the protecting-circuit shortcut,
so on such paths original output weights equal capped output weights.

## Exact one-edge budget estimate

For each horizontal grid edge e_k, retain the base iid original field X and
the cap auxiliaries V. Independently sample X'_{e_k} from G conditional on
the status of X_{e_k}, and leave all other original variables unchanged.
An implementation can use two independent replacement samples, one from
each conditional law, and select the sample for that status. Every individual
output original field X^k has precisely iid law G^E: its status has the original
Bernoulli law, conditional on that status its replacement has the original
conditional law, and this coordinate is independent of all other coordinates.
Its auxiliaries V also retain their independent original law.

All original statuses and auxiliaries are unchanged in this coupling. Hence
ALL L_e are unchanged, and the capped metric changes at at most the single
edge e_k. Conditional on the entire individual output (X^k,V), the hidden
old value has law G conditional on its revealed status. Therefore

    P(X_{e_k} in L_s | X^k,V)=p_{a,s}/r_s,
    p_* = min_s p_{a,s}/r_s >0.                                (1)

Let A_e^{alpha,beta}(H) be the source's bin/regularity/bigeodesic event in
the capped output, with usability tested by the original output weight.
On A the bigeodesic is wholly uncapped. Mark when A holds and the hidden old
weight belongs to the low band of its status. The common mark probability
thus obeys

    q_{alpha,beta} >= p_* P(A_e^{alpha,beta}(H)).                 (2)

On a mark, the new edge's cap weight equals its original output weight in
H_s, and the old original weight is at most a_s<b_s. Since the cap threshold
is the same, the old cap weight equals the old original weight as well.
The one edge increases by at least g, and all other cap weights are identical.

Consequently the source's base-comparator regularity argument applies with
no random change radius. A base ray from k either avoids e_k or uses it as
its first edge; in the latter case use its tail from the other endpoint.
Monotonicity and the finite-change label comparison preserve the relevant
rays and labels. Output regularity at both endpoints confines base rays with
offset H+1+s. Use the same spacing l(H)<=C_0(H+1), gain g, and radius1.
The deterministic budget and (2) yield

    P(A_e^{alpha,beta}(H))
       <= l(H)(r(beta)-r(alpha))/(g p_*).

Partition refinement and monotone convergence give E N_e(H)<=C(H+1) for the
number of distinct labels on usable, regular edges. No independence of marks
is needed. Source06 then uses its unchanged finite-tree edge-label count,
the original usable-path tail above, and cap all-ray cone bounds. It excludes
forks and identifies the common Busemann pair for equal bigeodesic labels,
conditional on opposite exceptional coalescence. No additional resampling
occurs in source06.

## Shared finite raises without changing any circuit

For each edge take the independent base X_e~G, a fresh trigger uniform U_e,
and independent samples Z_{e,o}~G|H_o and Z_{e,c}~G|H_c. Keep the cap auxiliary
V_e separate and unchanged. These collections are independent across edges.
Use exactly the source's height h(e), taper

    delta_h=eta/((h+2) log(h+2)),

and deterministic regions A_k(R). Choose eta so delta_0<=min_s p_{a,s}/2.
If X_e belongs to L_s, set xi_e=1 when U_e<=delta_h/p_{a,s}; otherwise xi_e=0.
On a success replace X_e by Z_{e,s}; otherwise retain X_e. Use these SAME
samples at every site, with one application in an overlap of regions.

Every replacement is upward and preserves the M-status. In each individual
or union environment, every circuit length L_e and every cap auxiliary V_e
is therefore exactly the base value. Cap weights can only increase, and can
change only at raised edges of the designated deterministic finite region.

The one-edge output density relative to G is

    lambda_h(t)=1+sum_s[-delta_h/p_{a,s} 1_{L_s}(t)
                       +delta_h/p_{b,s} 1_{H_s}(t)].            (3)

The four bands are disjoint; their integrals cancel within each status. Thus

    integral lambda_h dG=1,
    integral lambda_h^2 dG
       =1+delta_h^2 sum_s(p_{a,s}^{-1}+p_{b,s}^{-1}).            (4)

The density for a finite region is the product of (3), and the unchanged cap
auxiliaries have density1. The source's edge-height count and convergent series
sum_h(h+H_0+1)/((h+2)^2 log^2(h+2)) give the same uniform L2 and total-variation
bounds, with the constant in (4). Pushing these laws through Phi preserves
absolute continuity and cannot increase total variation. All individual and
union capped environments therefore inherit cap full-measure properties.

## Posterior product law after selecting a capped bigeodesic

Condition on the ENTIRE individual original output Y=(Y_e)_e and all the cap
auxiliaries V. For e in the region, the joint success/output measure is

    P(xi_e=1,Y_e in dt)
       =sum_s(delta_h/p_{b,s})1_{H_s}(t)G(dt).

Dividing by (3) yields

    P(xi_e=1 | Y,V)
       =sum_s 1_{H_s}(Y_e) delta_h/(p_{b,s}+delta_h).            (5)

The pairs (xi_e,Y_e) are independent across edges. The auxiliary V and exterior
outputs are independent of the interior pairs. The finite product conditional
kernel therefore extends to the entire output sigma-field by the same
monotone-class argument as the source. In particular the xi_e remain
conditionally independent given (Y,V). Circuit lengths depend on output
statuses already measurable in Y; they do not impose additional conditioning.

Select the witnessing capped bigeodesic as a measurable function of Phi(Y,V),
hence of (Y,V), alone. Conditional on this full output, its finite prefix is a
fixed list of distinct edges. Every usable edge of that prefix has success
probability at least

    delta_h/(max_s p_{b,s}+delta_0).

Since the entire selected capped bigeodesic is uncapped, each success on it
has new cap weight Y_e and old cap weight X_e: indeed X_e<=a_s<b_s<=Y_e<=K_e,
with the same K_e in all fields. Its cap gain is at least g. The usable-prefix
condition is also determined by (Y,V), and the total-variation bound transfers
its original-law probability exactly as in the source.

Consequently the source's Abel-summation lower bound for the conditional mean
of successes diverges like sum_j1/(j log j), and conditional variance is at
most that mean. There is a fixed near radius R_0 and for every requested toll
m an R(m) giving a near strict raise and cap gain at least m with conditional
probability at least3/4. The marking probability stays bounded below by p/4.
The near radius and horizontal spacing are independent of m. No posterior
formula is reused after subsequent base or neighbor filters.

## Union and final budget

All cap changes are confined to the source's deterministic A_k(R) and use the
same capped output sample on an overlap. The source's path-width argument
therefore leaves every edge of each selected bigeodesic unchanged when passing
from its individual capped environment to a two-site union; competitors only
increase. The finite-change label argument applies. A raised near edge at
the other site lies outside A_k(R) and has its base CAP weight in the first
individual environment. Its cap increase in the union is at least g by the
uncapping argument above. This is exactly the strict saving needed in the
source's no-repeated-marked-label detour proof.

The base comparator filter, finite same-bin neighbor filter, label-budget
telescoping, and successive limits in source08 depend only on these facts and
the common cap structural event. They yield p/8<=q_m<=l W_I/m for every m,
contradicting positive probability of a capped bigeodesic. Exact equivalence
of original and capped bigeodesics would then give the full moment-free
original conclusion.

The conclusion remains CONDITIONAL here: the all-ray structure, DH limiting
coupling, same-status downward lemma, cubic-wall coalescence and shape inputs
must be assembled and verified in a complete full-scope candidate. This note
does not substitute an application of the source theorem to a dependent cap
law, and does not assert that the original heavy-tailed metric has uniform
shape or linear Busemann functions. It records the exact interfaces by which
the source's final proof can be reused once those new inputs are proved.
