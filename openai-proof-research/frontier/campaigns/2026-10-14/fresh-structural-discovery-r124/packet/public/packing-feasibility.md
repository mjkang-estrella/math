# Full packing feasibility: source184

No theorem was selected or frozen. Everything below is preselection calculation. No partial, fractional, bipartite, large-parameter-only, or bounded-dimensional substitute is nominated.

## Exploratory scope, kept distinct from a frozen target

For each fixed integer r>=4, could constants C_r,D_r exist such that EVERY finite simple K_r-free graph G of maximum degree Delta>=D_r, EVERY integer k>=ceil(C_r Delta/log Delta), and EVERY correspondence assignment with exactly k entries per list admit k pairwise disjoint full proper correspondence colorings? Disjoint means that at every vertex each original entry is used in exactly one coloring. Edge constraints are arbitrary matchings between lists. Constants would depend only on r, not order, assignment or k. Triangle-free graphs are included. This is the full question investigated, not a theorem asserted here. Its finite low-degree portion could only be dealt with through a separately proved uniform bound; no such enlargement was used to declare this question solved.

Repeated application of the source one-color theorem, to the restricted lists, immediately obtains k-k0+1 disjoint colorings when k0 is its threshold. Constant numbers of colorings and partial packings with extra palette are therefore already compatible. That reduction stops precisely when the remaining lists fall below k0. No partial result is a fresh nominee.

## Strongest actual source contracts checked

The pinned Correspondence-Coloring-Graphs-with-a-Forbidden-Clique source supplies `lem:adjustment`, `prop:one-round`, the complete randomized round and its completion. The entry graph is K_r-free and every entry has at most one neighbor in each list. The adjustment lemma is already coordinatewise, not merely a scalar total-triangle bound. Its dual cone allows arbitrary nonnegative vertex prices AND support-rate prices, with multipliers equal to one still charged to listed support. Operations have bounded-radius support, bounded participation per part, bounded multipliers, and rates at each entry bounded by Lambda^4. The proof of this precise interface is stipulated; not all of its supporting triangle section was reread.

Write s_i for neighbor weight, d_i=w_i s_i, and t_i for twice weighted incident triangle mass. A multiplier has

    g_i = w_i f(m_i) + sum_(l~i) w_i w_l (m_i-1)(m_l-1),
    f(a)=a log a-a+1.

A singleton drop at i charges Lambda w_i-d_i and subtracts incident edge masses at its neighbors. The supplied finite family satisfies t_i+sum a_j g_i^(j)<=B d_i simultaneously. This is stronger than an unweighted independence theorem.

The actual round compensates independent activation and operation flags, retains the entropy identity, and uses newly colored neighbors to pay the expected potential increase. With K=16(B+2), its incident-edge gain K/8 exceeds B+1. The source uses weight caps Delta^-3<=w_i<=Delta^-.99, mass window [K/2,2K], tau=Delta^-.10, and concentration/LLL before trimming. Singleton drops have mean loss -tau a_i^- to first order. Trimming and completion certify one full coloring; they do not state exact entry marginals or simultaneous permutations of each list.

The independence companion was checked at its actual optimizer and closure. It already optimizes sum w_i(1-log w_i) minus edge mass, gives log(1/w_i)=s_i at a positive maximizer, and uses mean-preserving sparse multipliers to control edge mass, including overlapping-set cross-mass through a random split. Its actual weighted interfaces must be credited before proposing a weighted variant. They do not themselves assert a distribution on full transversals with prescribed uniform marginals.

## Slot representation and exact local cancellation

Represent a prospective packing by cells (v,c,j), where c is an original entry at v and j in {1,...,k} is a slot. A row R_(v,j) must choose one color; a column C_(v,c) may be used once. External edges H0 join forbidden original pairs in the SAME slot. Column edges H1 join different slots with the SAME v,c. H0 is a disjoint union of k copies of the original entry graph, hence K_r-free. Every triangle of H0 union H1 is wholly external or wholly a column triangle: an external edge changes vertex but not slot, while a column edge changes slot but not vertex. The row-host graph is G square K_k. It has large cliques even when G is triangle-free, so applying the source coloring theorem to that host graph would violate its hypothesis.

For a column C with mass S_C, its contribution at i is

    d_i^col = w_i(S_C-w_i),
    t_i^col = w_i[(S_C-w_i)^2 - sum_(z in C, z!=i) w_z^2].

For q equal weights w=K/q, t_i^col/d_i^col=(q-2)w. Absorbing this crudely into B adds approximately K, inconsistent with the UNCHANGED source inequality K/8>B+1. This rejects that estimate only. It is superseded by the stronger removal calculation below, not offered as a structural impossibility.

Fix a finite residual matrix at one vertex, with nonnegative cell weights, and consider two cells i=(c,j), l=(c,h) in one column, j!=h. Use independent flags with probabilities tau w_z and the source's mean compensator for column-neighbor deletion; keep only the coefficient of tau. For this local computation external flags and adjustment flags are absent. A single activation succeeds; multiple activations affect only the O(tau^2) remainder, with the matrix and weights fixed. Ignore removal of the focal row j, as in an upper bound for its surviving-row potential, and delete the opposite row h when it receives a selection. Products already killed by a column activation are not subtracted again.

The covariance contribution from common column neighbors is

    w_i w_l(S_C-w_i-w_l).

Activations at the OTHER entries of row h remove l while leaving this product provisionally nonzero, and contribute

    -w_i w_l(R_h-w_l).

Thus the combined coefficient is exactly

    w_i w_l(S_C-R_h-w_i).

When S_C=R_h, it is -w_i^2 w_l<=0. In the uniform q by q case it is -w^3, not a positive order-K triangle loss. This is a general first-order identity in a specified finite local update, not a theorem about the full packing dynamics, a uniform error bound as graph size varies, or a mathematical gate.

There is another compatible source operation. Apply `lem:adjustment` separately inside each slot of H0, with independent flags. One such multiplier touches at most one endpoint of any column edge. Consequently (m_i-1)(m_l-1)=0 on that edge, so its first-order centered covariance contribution vanishes. Singleton drops only remove column-edge mass. This prevents claiming that external triangle adjustment necessarily creates a new column covariance penalty. Source support bounds already apply per row; a slot operation meets each color column in at most one cell. No new adjustment lemma has been proved or is needed for these particular observations.

## The remaining full mechanism is not constructed

The above cancellations suggest tracking both row and column masses, entropy and external conflicts while selecting partial local permutations. They do NOT show that the required balancing can be maintained through the ACTUAL operations. Drops and trimming lose individual entries; the source potential permits mass windows rather than exact equalities. A first-order favorable drift at a balanced input is not a construction returning every output to that class. Conditioning on which rows and columns survived, collision errors, entropy charges and simultaneous concentration must be controlled with the same actual choices.

Most decisively, completion requires Hall for every subset of the residual rows at each vertex. Even arbitrarily close row/column mass balance does not imply Hall. For arbitrarily close balance, split into blocks of sizes a by (a-1) and (q-a) by (q-a+1), with a and q-a tending to infinity. Put 1/(a-1) and 1/(q-a+1) respectively on their cells. Every row has mass1; column masses are a/(a-1) and (q-a)/(q-a+1), both tending to1. Yet the first a rows have only a-1 neighbors. This is an abstract capacity diagnostic, NOT a residual matrix proved reachable from the source update and NOT a counterexample to the full question.

Exact doubly stochastic support would imply Hall by summing weights, but no repair maintaining that support and controlling the required entropy/external-conflict budget has been constructed. Merely invoking Sinkhorn scaling assumes away the support condition. A dual price for each row/column does not by itself maintain every subset's available neighbors after deletions.

There is also an endgame obligation. Whenever a residual column has mass at least K/2 and each cell has weight at most Delta^-.99, its vertex has at least (K/2)Delta^.99 remaining rows. Thus the unchanged fixed-Delta caps cannot simply be carried through a gradual depletion to a small nonempty local matrix. This is not impossibility: scales or an earlier exact completion could change. A complete multiscale invariant and compatible final permutation construction are not supplied here. No whole target is frozen on the basis of this local calculation.

## Actual primary interfaces and their limits

Cambie–Cames van Batenburg–Davies–Kang, [Packing list-colourings,2110.05230v2](https://arxiv.org/pdf/2110.05230v2), Theorem35 and Lemmas36–37, already use WHOLE uniform random permutations on one independent side of a bipartite graph, a k by k forbidden matrix at each opposite vertex, Hall zero-submatrix estimates, and a dependency/LLL bound. The threshold is logarithmic in the degree in the stated bipartite regime. The reduction is much stronger than repeated greedy colorings. Its proof uses independence of the chosen permutations on that side. For a general clique-free graph, independently assigning permutations to a nonindependent side does not ensure its internal edges; choosing those permutations through the source coloring law does not preserve the primary's independent uniform law. No replacement joint zero-submatrix estimate was proved. Lemma37's conditional-column estimates were partly read; its whole tail proof was not, so no stronger arbitrary-dependent version is credited or excluded.

Cambie–Cames van Batenburg, [Fractional list packing for layered graphs,2410.02695v1](https://arxiv.org/pdf/2410.02695v1), definitions3.3–3.7 and Lemma4.2, were checked to distinguish exact uniform entry marginals from an independent set taking a fraction of each list. These are different objects. No fractional-DP title was treated as an exact marginal packing theorem. Its later pathwidth proofs were not read.

Cambie–Cames van Batenburg–Zhu, [Disjoint list-colorings for planar graphs,2312.17233v1](https://arxiv.org/pdf/2312.17233v1), full Lemmas7.1/7.3 and Remark7.7, give a compatible exact-marginal deletion/gluing operation when each inserted vertex has at most ONE outside neighbor. The explicit conditional formula in Lemma7.3 was also visually checked. Remark7.7 shows that a fixed boundary distribution can fail to extend with two boundary neighbors. It does not refute a globally chosen fractional packing. No arbitrary clique-free layering satisfying the lemma was constructed. The fractional route is a comparison, not a repaired nominee.

Actual r114's screen184 already records the no-floor local-degree palette obstruction and its primary source; r121 repeats it. That is a different question from the global-Delta full packing here. No local-degree variant is offered. Construction/alias searches were extended after these calculations to permutation packing, zero submatrices, doubly stochastic/Sinkhorn/Birkhoff and disjoint-list terminology, before sealing. They did not certify absence or establish priority. All conclusions in this file remain author feasibility work.
