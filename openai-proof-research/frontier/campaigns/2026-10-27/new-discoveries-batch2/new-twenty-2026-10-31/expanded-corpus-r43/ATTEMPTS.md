# Sustained routes and exact gaps — r43, 2026-11-01

No discovery is proposed for acceptance. No Lean theorem or surrogate endpoint was manufactured. All computations below are diagnostics, not semantic certificates. Three substantive routes received new mathematical work; the hypercube route stopped upon reading its existing refutation.

## 350316: projective sign-vector Sperner property (rank 1)

Primary body: Karp–Machacek, arXiv:2104.02786, relation (1.1), §5 Theorem5.2, Conjecture5.3, Proposition5.4 including its proof. Elements are nonzero vectors in {0,+,-}^n modulo global negation, with at most ell changes after deleting zeros. Choose the representative whose first nonzero sign is +. Order is sign-preserving support extension, allowing a global sign choice before comparing representatives. Rank is support size. This is P, not the exactly-ell-change poset R whose strong Sperner theorem is already proved.

The exact target is the full assertion for every 0<=ell<n, not additional finite orders. Rank sizes are C(n,r) sum_{j<=ell} C(r-1,j); their log concavity is source-known and does not imply Sperner by itself.

Mechanism A: construct matchings between adjacent ranks saturating the smaller rank; rank unimodality then glues them into chains passing through a largest rank and bounds all antichains. `poset_diagnostic.py` constructs actual projective cover graphs by deleting one sign and canonicalizing. All adjacent rank pairs saturate in six cases n=9,10 and ell=2,3,4 (`poset-diagnostic.log`). This extends bounded source evidence, not its universal conclusion. Finite cases are not nominated for credit.

Mechanism B, stronger: seek uniform normalized flows. For adjacent ranks of sizes a,b use integral network capacities b from source to each lower vertex, a to sink from each upper vertex, and ab on cover edges. Required total ab is equivalent to a uniform-marginal coupling and hence the normalized matching property. `poset_flow.py` finds full flows in all the same rank pairs (`poset-flow.log`). These are external SciPy computations without a Lean checker and are not certificates.

Mechanism C: try to extend Proposition5.4's ell=1 formula by splitting weight equally between the admissible signs at each zero coordinate. This makes each lower vertex's outgoing weight n-r. It fails to make the upper sums constant: `poset_local_weights.py` gives n=6,ell=2,r=3 upper sums 2 and 5/2 at representatives (1,0,0,1,1,1) and (1,0,0,-1,-1,-1). Thus simply reusing the source flow is not a proof.

Precise remaining sufficient lemma: for every subset A of support-r projective sign vectors with <=ell changes, |N(A)|/W_(r+1) >= |A|/W_r. Alternatively prove only the cardinal Hall inequalities on each side of a largest rank. A recursive insertion flow must account for runs and zero gaps; no such nonnegative universal formula was found. A future Lean proof must include the quotient/canonical representative bridge, cover relation, antichains and matching-to-width argument. Finite matching success is insufficient.

## 350625: Staller's largest legal submove (rank 2)

Primary body: Bujtas–Rote–Tuza, arXiv:2105.03890, §2 game rules including (*), Theorem6 and proof, §5 recursion equations(1)–(6), Theorem11 and Lemma12 proof, final Conjecture3. New source-body reading verifies that arbitrary partial covering functions are explicitly included. Published-version search lead renumbers this Conjecture7.4; that published PDF body was not independently fetched/audited in this pass.

Each player spends total1 per turn unless full coverage ends the game. A submove at v may increase t(v) by w when some incident edge's unsaturated load can increase by exactly w. Thus the maximum legal amount is min(remaining turn budget, max incident edge residual). Staller maximizes total terminal weight; Edge-hitter minimizes it. Choosing maximum submove weight does not require choosing the vertex with globally largest weight.

Mechanism A: search near-terminal states, where all legal remaining play fits in Staller's current turn. In n=5 hypergraphs with edge sizes2,3 and t_i in {.42,...,.49}, each vertex can receive at most .16, so total additional legal weight is <=.8. Greedy play needs each vertex at most once, since a maximum submove saturates all incident edges. Exhaust all120 vertex orders, compare a smaller first submove followed by greedy completion. `game_diagnostic.py` finds no gap in300 seeded random states, using prefix fractions1/4,1/2,3/4. Edges of size3 are already saturated in this sample, so this is chiefly a graph/terminal-turn test. Not exhaustive over weights or states.

Mechanism B: test move-boundary interaction with a quarter-grid minimax. `game_grid.py` allows arbitrary sequences of positive grid submoves, alternating turns at budget exhaustion. It compares unrestricted grid Staller with Staller restricted to largest grid-legal weights, with unrestricted grid Edge-hitter in both games. All nonempty simple graphs on4 vertices and56 seeded size2/3 hypergraphs on5 vertices are tested at all625 or3125 grid cover states. No gap was found. This is not a continuous-game equivalence theorem: Edge-hitter's off-grid moves may change both values. No finite-grid statement is offered as the literal conjecture.

Mechanism C: source recursion proves rational piecewise-linear continuous value functions, not that maximizers occur at the largest legal endpoint. The needed local quantity is F(w)=w+T(update_v(load,w),budget-w). Even if it is affine within each cell, a global maximum may occur at an internal breakpoint, and the source proves no suitable endpoint monotonicity. One must either compute exact polyhedral value functions for a candidate and prove a strict continuous gap, or prove a global exchange/endpoint lemma for Staller over all vertex choices. Source Theorem6's merging of repeated vertices preserves the final loads for an individual move; it does not turn arbitrary choices into greedy submoves or settle all future play. This is the precise remaining strategic gap. No witness survived to formalize.

## 350596: chordal k-path cover bound (rank 3)

Primary body: arXiv:2105.02018 §4, Theorems18/19 with proofs; §5.3 Conjecture29. Paths have k vertices, need not be induced. A hitting set is exactly the complement of an induced subgraph containing no ordinary k-vertex path. Chordal means no induced cycle of length>=4. Target is psi_k(G) <= (omega-1)n/(omega+k-2), all k>=3.

Mechanism A: strengthen the source's clique-tree separator induction. To use the desired ratio directly, a sufficient removable-block lemma would supply U,S with S subset U, no edges between U\S and G\U, G[U\S] P_k-free, and |S|/|U| <= (omega-1)/(omega+k-2). Then apply induction to G\U. The source's omega-vertex bag bound supplies only omega/(omega+k-1). Removing one fewer separator vertex requires control over an additional boundary vertex's paths through several branches; this control is not supplied by the source argument and was not established here.

Mechanism B: the two-largest-color-classes argument gives ratio 1-2(k-1)/(omega*k). For k>=3 this reaches the target only when omega<=2: comparison reduces to (omega-2)(k-2)<=0. Those forest/edgeless cases are already source-known. Theorem19 exceeds the conjectured ratio by (k-1)/((omega+k-1)(omega+k-2)), so it is not a full-scope bridge. No credit for re-formalizing these cases.

Mechanism C: exact recursive hitting search over800 generated graph/parameter pairs, 200 seeded chordal graphs on12/14/16/18 vertices and k=3,4,5,6. Graphs are built by adjoining a simplicial vertex to a subset of a previously stored clique, giving a known perfect elimination order and exact clique number. Recursive solver finds a k-vertex path and branches on deleting each of its vertices, with memoization; the recurrence is mathematically exact but not Lean-certified. `chordal-diagnostic.log` records no counterexample. Sample is structurally biased and far from exhaustive. A uniform block lemma or an explicit violating graph plus exact chordality/clique/path-transversal Lean bridges remains necessary.

## Routes stopped on existing source results

350552: Wagner arXiv:2104.14516 §3.1 Conjecture3.1 is exactly the reserved dimension-stability claim. The next page already refutes it with n=6,k=4,B={1000,1111,1001,1011,0110,0001,0010,0111}; complement in dimension4 needs>=3 planes, dimension6 needs<=4. Four displayed hyperplanes are (-x2+x5+x6=1), (x2-x3+x6=1), (x1+x2-x4+x5+x6=2), (2x1-x2-2x3+2x4+x5-x6=0). The upper construction is explicit; the lower two-plane exclusion is asserted as straightforward case analysis, not expanded in this paper. Thus no new refutation is available here, and that lower-case proof was not independently completed. Source proof presentation and its gap are reported honestly. Do not revive a new smaller witness as new family credit.

350266: Das–Ghalavand–Ashrafi arXiv:2103.17147 Conjecture2.2 is proved by Theorem3.5 over the stronger range0<=nu<=n-2. Read proof decomposes Sombor sum at a universal vertex, using Lemmas3.3/3.4 and the cited Lemma3.2 universal-vertex result. Theorem3.5 and local lemmas inspected; referenced predecessor proofs were not audited. The source already resolves the exact target5<=nu<=n-2.

350409: Haslegrave arXiv:2104.06959 Conjecture1.1 is refuted by §2 Theorem2.2 and its actual proof: a chain of s cycles of length2k+1 has edge differences in{1,2k}, and Theorem2.1's injective cycle-label count forces arbitrarily large sum index. Choosing s large makes ceil(sum/2)>2. Definition and proof bodies read; no new counterexample credit.

## Other new primary reads (not full exclusions)

350275: arXiv:2104.00778 §1.2 Conjecture2 and §5 Theorem10 proof read. Polynomial method covers k-ell not dividing ell!, plus prime-power k-ell from prior work; no universal remaining-case bound established. Source has no additional n-size hypothesis in its displayed conjecture; do not manufacture a small-n correction. All original Frankl–Tokushige book proof bodies remain unread.

350635/350636: arXiv:2105.04137 §1.2 Conjectures1.10/1.11 and augmentation discussion read; Theorem4.2 closing argument and Corollary4.3 inspected, giving inv(Q7)=3. This is a partial-family statement, not the arbitrary-n endpoint. Prior current-literature resolution search on these inversion targets was not completed, so they are not novelty-cleared. No finite-order variants nominated.
