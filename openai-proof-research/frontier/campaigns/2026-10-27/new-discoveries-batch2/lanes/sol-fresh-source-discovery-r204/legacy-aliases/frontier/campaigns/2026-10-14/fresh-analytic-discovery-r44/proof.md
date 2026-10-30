# T221R: regular-degree hierarchy formula — author proof

Author: Myeongjin Kang (no affiliation). Original text CC BY 4.0.
This is an author-side proposed proof, not an independent proof or
contribution verdict. The exact target was frozen in `original-scope.txt`
before this proof was assembled. All source results below refer to the
pinned family-221 manuscript; their truth is stipulated. In particular,
this proof does not audit its finite-tree identities or decorrelation.

## 1. Statement and dependencies

The statement is exactly `original-scope.txt`. Put θ(s,t)=βJst and h=βH.
The partition function is the sum, over all labelled vertex spins, of
exp(sum of edge scores plus sum of vertex scores). A configuration loop
contributes βJσ_i² in the usual way. Fields and edge couplings are iid
within their respective families and mutually independent of the graph.

Write B_d for the functional in the scope file and b_d=inf B_d over its
entire finite-hierarchy class, including depth zero. We prove
lim n⁻¹ E log Z_n=b_d, first for bounded θ,h in the configuration model,
then for arbitrary integrable physical disorder and uniform simple graphs.

External upper-bound input: Lelarge–Oulamara, *Replica Bounds by
Combinatorial Interpolation for Diluted Spin Systems*, arXiv:1708.02457v2,
Theorem 3, with its §§4–6 proofs. For bounded θ,h it gives
limsup n⁻¹ E log Z_n≤B_d for every finite hierarchy. Its degree law is
δ_d and its edge-size law is δ_2. Its hypotheses hold: in their
factorization take a=cosh(βJ), b=tanh(βJ), f(s)=s. Symmetry of J makes
all odd moments of b zero and all even moments nonnegative. Both degree
moment assumptions are automatic. Their spin sum, instead of the
normalized spin average in our V_s, supplies our log 2. Their recursive
conditional power means and independent label processes are precisely the
ones in the scope file; bounded interactions make messages unrestricted.
No claim that this upper bound is new is made.

For the lower bound we use the source's generic insertion calculus
(`tree:insertion`, `tree:log-expansion`, `tree:regular-shapes`), the
score-to-prescribed-tree identities of perturbations.tex, its
`decor:overlap-concentration`, and `comp:encoding`/`comp:patterns`.
Section 5 below verifies the changed empirical-coordinate and disorder
hypotheses. We do not invoke the source's Poisson graph cavity increment.

Throughout Sections 2–7, |θ|≤B and |h|≤H. Constants may depend on
d,B,H and on a fixed perturbation type or depth when explicitly stated.
They never depend on n,q or perturbation parameters in their specified
intervals. All n have dn even; q is even and q=o(n).

## 2. Deficient configurations and uniform bounded changes

Define C(n,q) as follows. Choose uniformly q distinct cavity vertices A.
At each vertex of A remove one uniformly chosen port from its d labelled
ports, independently. Pair all remaining dn−q ports uniformly. The
missing-port choices are part of the random experiment. In particular,
one must not fix port d as the absent port when interpreting the inverse
completion count in Section 3.

Attach the source's perturbation family, with total Poisson intensity s,
by choosing every perturbation site uniformly in A. The factor is
1+t_ν gσ_i+u_ν g_0 S_0, lies in (1/2,3/2), and has precisely the source's
finite auxiliary mark process and type probabilities c_ν. The physical
disorder, all root counts/types/sites, and the graph are quenched; the
marks are integrated at their assigned depths. At depth L use
m_j=j/L, j=1,…,L−1. Denote the root log partition function X_0 and its
expectation P(n,q,s;u,L). Multiplicative bounds at the leaf are preserved
by every conditional power mean. Thus changing k edges, k fields, or k
perturbation factors changes X_0 by at most Ck (with the appropriate
constant for each kind). Unused independent mark coordinates integrate
out when a factor is removed.

Uniform matching deletion fact: deleting a prescribed pair of ports from
a uniform perfect matching, and pairing their former partners if the two
deleted ports were not paired together, gives a uniform matching on the
remaining ports. Indeed every target matching has the same number of
preimages: one with the deleted ports paired together, and two for each
target edge. Repeating this proves the analogous assertion for every
even prescribed set of ports. Consequently C(n,q) can be coupled to a
regular configuration on n vertices with O(q) edge changes. It follows
uniformly in u,L that

    |P(n,q,s;u,L) − E log Z_n| ≤ C(q+s).                 (2.1)

Conditional on A and the removed ports, expose a uniform matching one
pair at a time. If the currently exposed port is paired with y rather
than z, the remaining laws can be coupled by switching at most two
edges. Hence conditional expectations of X_0 differ by a constant.
The matching Doob martingale has O(n) bounded differences. Conditional
on a matching, edge couplings, fields, and the finite list of perturbation
types/sites are independent inputs; bounded replacement and
Efron–Stein give variance O(n+s). Conditional means as a function of the
Poisson total count are Lipschitz, and so contribute O(s). Conditional
expectations given A and missing ports are identical by vertex and port
symmetry, including iid fields and uniform cavity-site perturbations.
Thus

    Var X_0 ≤ C(n+s).                                  (2.2)

The same proof applies to X_0+2n_ν u_ν². The addition contributes only
O(s), including covariance by the elementary variance inequality. These
bounds hold uniformly in L and u (constants in the added correction may
depend on its fixed type interval). They concern the complete root log,
not an individual realized auxiliary leaf partition function.

## 3. The bond-completion density and its covariance estimate

Start with C(n,q+2d). Choose 2d of its cavities uniformly, and match
their missing ports uniformly to form d additional edges. Keep the
remaining q cavities. For now omit perturbations. Conditional on the
final cavity set A and its missing ports, the completed matching has the
law of C(n,q) tilted by

    W = M_d / E M_d,                                   (3.1)

where M_d is the number of unordered sets of d configuration edges,
each nonloop, with pairwise disjoint endpoints, all outside A. Edges
are distinguished by ports, including parallel edges. To prove (3.1),
delete such a set of d edges from the final matching. Its 2d endpoints
are precisely the filled cavities, and each deleted endpoint port is the
former missing port there. This is a bijection between inverse histories
and the counted edge sets. Every inverse history has the same probability:
the cavity-set probability, independent uniform missing-port probabilities,
uniform matching probability, filling-subset probability and pairing
probability depend only on n,q,d. Normalization proves (3.1). Uniform
random missing ports are essential to this count. New couplings are iid,
so (3.1) remains true for the weighted graph, with W depending only on
its matching.

Here is a uniform quantitative bound on this tilt. Let E_hh count edges
having both endpoints in A, including loops, and let L_ff count loops
whose vertex is outside A. The number E of nonloop edges having both
endpoints outside A is exactly

    E = (dn−q)/2 − q(d−1) + E_hh − L_ff.                (3.2)

Expose all q(d−1) cavity ports first. Switching a partner changes E_hh
by at most two, so Var E_hh≤Cq. Also E L_ff²≤C: write the loop count as
the sum over at most n binom(d,2) candidate port pairs. A single candidate
occurs with probability (dn−q−1)⁻¹; two disjoint candidates occur with
probability [(dn−q−1)(dn−q−3)]⁻¹, and overlapping distinct candidates
cannot both occur. These bounds prove the second-moment assertion.
Therefore Var E≤C(q+1).

The number of ordered d-tuples of available nonloop edges is E^d.
Tuples with a repeat or a shared vertex number at most C_d n^(d−1),
because degree is bounded and d is fixed. Dividing the valid ordered
tuples by d! gives the uniform, pointwise estimate

    M_d = E^d/d! + R,       |R|≤C_d n^(d−1).            (3.3)

Removing L_ff in (3.2) is necessary: no uniform small remainder for a
count allowing arbitrary loops would follow merely from bounded degree.
The map x↦x^d is C_d n^(d−1)-Lipschitz on [0,dn/2]; applying the
independent-copy variance identity to (3.3) yields

    Var M_d ≤ C n^(2d−2)(q+1).

Moreover E E≥dn/2−O(q)−O(1), so Jensen and (3.3) imply
E M_d≥c_d n^d for large n. Hence

    Var W ≤ C(q+1)/n².                                (3.4)

There is also the exact deterministic normalization (parent author-side
calculation, subsequently checked here): with N=dn−q,

    E M_d = binom(n−q,2d) (2d−1)!! d^(2d)
                       / product_{j=1}^d [N−(2j−1)]. (3.6)

Choose the 2d full vertices, a perfect matching of these vertices, and
one of d ports at each endpoint. The probability of the d prescribed
pairs is the reciprocal denominator. Summing gives (3.6), independently
confirming both the normalization and its order n^d.

If X_0 is the q-cavity root log with perturbation mean O(n), its law
conditional on a matching is the ordinary law just specified. Apply
Cauchy–Schwarz to E[(W−1)(X_0−E X_0)] and (2.2):

    |E[W X_0] − E X_0| ≤ C sqrt((q+1)/n).              (3.5)

This is an expectation estimate for an extensive statistic. A total
variation estimate multiplied by its O(n) size is not being used.

## 4. Star completion, perturbation repair, and increments

From the same C(n,q+2d), add two vertices, choose an ordered list of
2d distinct cavities uniformly, and join their missing ports to the d
labelled ports of each new vertex. Add iid fields at the new vertices.
Conditional on the q remaining holes A, the resulting graph has the
law of C(n+2,q) conditioned on the event G that the 2d new ports have
distinct old full-vertex neighbors. The new vertices are full. For the
scalar root log one can fix A to lie among old vertices, by exchangeability.
An inverse history is obtained by deleting the new vertices and their
edges; all inverse histories have equal probability. This proves the
conditional-law assertion, including the randomized missing ports.

There is an exact coupling of a uniform matching with its law conditional
on G whose expected number of changed edges is O(q/n). Process the 2d
new ports x in their fixed order. Previously exposed pairs are frozen.
The legal partners for x are all ports at old full vertices not previously
used as neighbors; their number is d(n−q−j+1) at step j, independent of
the previous partner identities. If its current partner z is legal, keep
it. Otherwise choose a uniform legal port y; if y is currently paired
with w, switch {x,z},{y,w} to {x,y},{z,w}.

For completeness this is exact conditional resampling. Conditional on
prior frozen pairs the remaining matching is uniform. For a fixed legal
y and a fixed target matching containing {x,y}, there is its unchanged
preimage, and, for each illegal z, exactly one switched preimage obtained
by reversing the switch using z's partner in the target. The latter has
the extra probability 1/(number of legal partners). Thus the total
preimage weight is independent of y and of the target matching. The
output is uniform conditional on x having a legal partner. Future legal
set sizes depend only on the step number, so iteration gives uniformity
conditional on G, rather than an unintended additional bias.
The fraction of illegal remaining ports is O_d((q+1)/n). There are only
2d steps, each changing at most two edges. The claimed expected edit
bound follows. Couple iid couplings on common edges, resampling them
on the changed edges, independently of the matching transformation.
Uniform q-cavity perturbations stay unchanged. The root-log difference
in expectation is consequently O(q/n), not O(n P(Gᶜ)).

Now put q_n=2 floor(n^(9/10)/2), s_n=n^(3/4), ignoring the finite
initial segment where too few cavities are available. At a good index n,
q_{n+2}=q_n=q. Use C(n,q+2d), perturbed at mean s_n, as the common
reservoir. Delete its perturbation factors whose sites are among the
filled cavities. Poisson thinning leaves independent uniform perturbations
on A with mean s_n q/(q+2d). Augment by independent factors to mean s_n
on the bond side and s_{n+2} on the star side. The expected number of
changes is

    O(s_n/q + |s_{n+2}−s_n|)=o(1).                    (4.1)

The repaired perturbations conditional on A are independent of the
completion matching, so (3.5) and the star coupling apply to their full
root logs. Removing/adding auxiliary marks has the bounded cost explained
in Section 2. Thus, writing P_n=P(n,q_n,s_n;u,L),

    P_{n+2}−P_n = 2 log 2 + E log Y_{*,0}
                            − E log Y_{b,0} + o(1),   (4.2)

uniformly in u,L at good indices. Here the reservoir is the ORIGINAL
one, before repairing perturbations; Y is the source insertion recursion
under its tilted kernels. The two insertions at a terminal spin leaf are

    A_* = product over a=1,2 of
          [ (1/2) sum_{ε=±1} exp(h_a ε)
                         product_{j=1}^d exp(θ_aj(σ_i(aj),ε)) ],
    A_b = product_{j=1}^d exp(θ_j(σ_i(2j−1),σ_i(2j))).

Each uses 2d uniformly sampled distinct cavity labels. Replace these
labels by iid uniform labels of the reservoir: their collision probability
is O_d(1/q), and the logarithm of either insertion recursion is bounded
by C=2H+2dB. This contributes another o(1) to (4.2).

All increments P_{n+2}−P_n are uniformly bounded, including bad indices.
Indeed eventually q_{n+2}−q_n is either 0 or 2. To change q by two at
fixed n, choose two uniform full vertices and one uniform port at each;
delete these ports, splicing former partners. Uniform matching deletion
gives exactly C(n,q+2). Adding the two new possible perturbation sites
changes expected O(s_n/q) factors by Poisson thinning/augmentation. There
are O(1) edge changes. Combine with (4.2), whose insertions are bounded,
to get the asserted uniform bound. The number of bad indices up to N is
O(N^(9/10))=o(N).

## 5. Localized prescribed-tree identities and decorrelation

This is the source-transfer interface, stated explicitly to avoid applying
its Poisson-graph theorem to an unverified regular graph model. At each
reservoir root use the set I of its q_n+2d cavities as the observed
coordinates. On every prescribed replica tree define

    R_S = |I|⁻¹ sum_{i∈I} product_{a∈S} σ_i^a.         (5.1)

All replicas still consist of all n spins; only the coordinate average
is changed. The source's generic finite-tree calculus is for arbitrary
probability transition kernels and does not require a physical graph law.

The proof of `pert:concentration` has two inputs about physical disorder:
(i) bounded replacement preserves root-log bounds, and (ii) the root log
plus its convex correction has variance O(n). Both were proved in (2.2).
Its thermal-variance differentiation is unchanged: the same Poisson
counts, marks, factors and exponents give

    X'_0=<D_ν>,
    X''_0 ≥ m_1 Var(D_ν | root) −4 n_ν.

For λ_ν=c_ν s_n, integration over the fixed type interval gives thermal
error O_{ν,L}(λ_ν^−1/2); this constant includes m_1^−1/2=√L and is
not uniform in L. The convex derivative argument, with ρ=n^−1/8, gives
root error bounded by

    C_ν[ sqrt(n)/(ρ s_n) + ρ + s_n^−1/2 ] →0.         (5.2)

This proof is conditional on the fixed cavity set and removed ports and
then averaged; permutation symmetry makes the conditional means equal.
It is uniform in all other parameters. There is no factor n/|I| in
(5.2): intensity is s_n, and every Poisson site is sampled from I.

In the next part of perturbations.tex the Palm identity inserts one
uniform site with its full independent mark process. In this model that
site is uniform in I. Its averages of replica-spin products are exactly
(5.1). Thus every displayed insertion, Taylor coefficient, independent-sign
branch selection and prescribed-tree identity in that proof holds with
N⁻¹ sum over all spins replaced by |I|⁻¹ sum over I. No edge is inserted
in this Palm operation. The parameters t_ν=j⁻¹ and u_ν∈[j^−j,2j^−j]
and their order of limits are unchanged. Bounds for Taylor coefficients
use only |σ_i|≤1 and the factor bound, not the geometry of the index set.

For clarity, the subsequent source decorrelation theorem is applicable
for the following exact reason, not merely an analogy. Its contraction,
projection, and martingale calculations take place in the finite Hilbert
space with scalar product (1/N)sum_i v_i w_i, and in the auxiliary
probability kernels. Replace that Hilbert space by R^I with scalar product
|I|⁻¹ sum_{i∈I}v_i w_i. Every spin vector still has norm one, all kernel
conditional expectations are contractions, and the marked identities just
verified give its hypotheses. The charging/regular-shape estimates depend
only on depth and prescribed topology. Its induction therefore yields,
on any sequence with all fixed-type errors tending to zero and all finite
moments converging,

    lim_{L→∞} limsup_{n→∞} A_{L,η} Var(R_S)=0          (5.3)

for each prescribed topology and fixed interior separation η; singleton
variance vanishes already at fixed L. The n limit precedes L. Nothing is
asserted about concentration of averages over the full n-vertex set.

## 6. One sequence with low increments and every identity

Work in one admissible parity class (only even n if d is odd, each of the
two classes if d is even), and let f be its unperturbed liminf pressure.
By (2.1), uniformly in L,u,

    liminf n⁻¹ integral P_n dπ = f.                   (6.1)

There are infinitely many good n with
integral(P_{n+2}−P_n)dπ≤2f+ε. Otherwise every sufficiently large good
increment exceeds 2f+ε, while the bad increments are bounded and their
number is o(n); telescoping in this parity class contradicts (6.1).

For fixed L choose these indices increasing sufficiently rapidly that
sum_{ν≤j} integral e_{ν,n_j}dπ≤j^−3 in the reservoir. The set G_j on which
every error e_{ν,n_j}≤j^−1, ν≤j, has measure at least 1−j^−2. Uniform
boundedness of increments shows that their conditional mean on G_j is
at most 2f+2ε for large j. Choose a deterministic parameter vector there
whose increment is at most this bound. A further diagonal subsequence
makes all finite products of overlaps on every fixed prescribed tree
converge; they form a countable family and lie in [−1,1]. This is precisely
the source's parameter-selection argument with the two-vertex increment
and the sparse bad indices accounted for. For each L the sequence may
differ, and f always remains the liminf of the original entire parity
class. We have

    Δ_n≤2f+2ε,  all fixed e_{ν,n}→0.                  (6.2)

## 7. Trial encoding and the lower bound

At fixed n,L and the selected parameters, include an independent uniform
cavity i∈I in the full reservoir root. At its terminal auxiliary prefix
put x=atanh<σ_i>, which is finite because all finite-system weights are
strictly positive. Iterating conditional laws backward gives the source
`comp:encoding` trial ζ_{L,n}∈M_L. Independent copies of the ENTIRE
reservoir root and prefix construction give independent trial labels.
For every prescribed tree and S its one-label spin product has expectation
E R_S. This is not conditional independence of physical sites.

The empirical distribution of a spin pattern e∈{−1,1}^k at a uniform
cavity is

    π(e)=2^−k sum_{S⊆[k]} R_S product_{a∈S}e_a.

For a bounded-by-one observable using a iid cavity labels, replacement
by independent trial labels changes its expectation by at most
a sum_{S≠∅} E|R_S−E R_S|. This follows by the telescoping total-variation
bound for product measures, exactly `comp:patterns`, now on I.
The source regular-shape estimate and (5.3) imply, for each fixed k,

    lim_{L→∞}limsup_n E_{Q_k}sum_{S≠∅}E|R_S−E R_S|=0. (7.1)

More explicitly its bound is C_k[η+L⁻¹+sum_U
(A_{L,η}Var R_U)^(1/2)], summed over the finitely many induced
topologies. First take n, then L, then η↓0.

Both insertions in (4.2) lie in [e^−C,e^C]. Set z=cosh C and
c=tanh C<1. Write A=z(1+D), |D|≤c. Apply the source logarithmic
expansion. At fixed order k the integrand uses at most 2d cavity labels,
so (7.1) makes its reservoir-to-trial error vanish. The tail is bounded
uniformly in n,L by sum_{k>K}c^k/k on each side. Hence the insertion
logarithms agree in the ordered limits, with no unbounded count cutoff
required here. Independent label groups factor through every conditional
power mean; the two-star trial logarithm is twice E log T_0 V_s and the
d-bond trial logarithm is d E log T_0 V_e. Consequently

    lim_{L→∞}limsup_n |Δ_n−2B_d(ζ_{L,n},m^(L))|=0.    (7.2)

Combining (6.2) and (7.2), b_d≤f+ε. Let ε↓0. The upper bound in
Section 1 yields limsup pressure≤b_d≤liminf pressure in each admissible
parity class. Both classes have the same b_d, so convergence holds over
all admissible sizes, for bounded physical disorder.

## 8. Simple graphs and integrable disorder

For fixed d the probability that a uniform regular configuration is
simple stays bounded below by a positive constant. This is, for example,
Janson, arXiv:math/0609802v1, Theorem 7.1 and Remark 7.2, whose actual
factorial-moment proof specializes as follows: loop
indicators have limiting total mean (d−1)/2, double-edge indicators
have limiting total mean (d−1)²/4; any fixed collection of disjoint such
patterns occurs with the product pairing denominator, while overlapping
patterns contribute O(1/n). Their joint factorial moments converge to
independent Poisson moments. Higher edge multiplicities are covered by
the double-edge indicators. The standard factorial-moment proof (or its
finite Bonferroni truncation followed by increasing truncation order)
gives P(simple)→exp(−(d²−1)/4)>0. This calculation depends only on fixed
d and covers both parity classes. Conditional on simplicity, the graph
is uniform simple and the couplings and fields keep their iid laws.

For bounded disorder, Var(log Z_n)≤Cn by the same matching exposure as
(2.2). If S is simplicity, Cauchy–Schwarz gives
|E[log Z_n|S]−E log Z_n|≤sqrt(Var(log Z_n)/P(S))=O(sqrt n).
Dividing by n proves the same formula for simple graphs.

Finally clamp J to [−K,K] symmetrically and H to [−K,K]. Set
δ_J=βE|J−J_K| and δ_H=βE|H−H_K|, which tend to zero. Edgewise
comparison of partition functions, valid for loops too, gives uniformly n
and in either graph model

    |F_n−F_{n,K}|≤(d/2)δ_J+δ_H.

For every trial, each site insertion has expected log change at most
dδ_J+δ_H and each edge insertion at most δ_J. Multiplicative bounds
survive all power means with physical disorder held fixed. Therefore

    |B_d−B_{d,K}|≤(3d/2)δ_J+δ_H                      (8.1)

uniformly over all finite depths, all messages and all exponent choices.
The same bound holds for their infima. Apply the bounded-disorder result,
then let K→∞. This proves the full integrable-disorder statement and
completes the proposed proof of the unchanged target.

## 9. Attribution and exact status

The finite hierarchy calculus, colored identities, multioverlap
decorrelation and empirical pattern comparison are source-essential paid
operations. The regular upper bound is paid by Lelarge–Oulamara. Generic
cavity opening and insertion in regular graphs is antecedent work of
Coja-Oghlan–Perkins, whose finite reservoir parameter is taken large
after the thermodynamic limit. The author-added construction here is the
mesoscopic distinct-cavity pool, its localized perturbation interface,
and the covariance estimate for the nonuniform bond completion, with
sparse-size and parity selection. Whether this constitutes a substantial
contribution rather than a technical application requires a separate
independent contribution review. No such verdict is asserted here.
