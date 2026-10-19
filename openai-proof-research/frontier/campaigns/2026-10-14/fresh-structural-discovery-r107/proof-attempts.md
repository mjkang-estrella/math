# T174D: proof development and remaining bridge

Status: the full frozen target is unresolved. No candidate theorem, independent gate, nomination, or count credit. The scope in scope.md is unchanged. The all-order auxiliary obstruction is in frame-obstruction.md; it is not a replacement target.

## 1. What follows from the pinned source, and what does not

Let D satisfy the frozen hypotheses with directed connectivity k. Forget directions but keep every labelled arc as a separate undirected edge, obtaining U. Eulerian balance makes |delta_U(S)|=2|delta_D^+(S)|, so U is 2k-edge-connected. Source174 thm:main gives an undirected spanning tree T0 with

 |delta_T0(S)| <= (C0/(2k))|delta_U(S)| = (C0/k)|delta_D^+(S)|.

This is already the desired all-cut count; it says nothing about reachability from the prescribed root. Keeping each selected arc's direction need not give an out-arborescence. Reorienting its edges is legal only where D contains the reverse arcs. In a symmetric digraph it is legal, and the full symmetric subclass is a paid routine consequence. That subclass is not nominated.

The source's actual prop:step is stronger than just its headline: a single selected subset controls a cut matrix and an isotropic rank frame, retaining almost half of an undirected tree packing. Lemma lem:projected-trace-packing tests projections off within-part incidence spans, giving undirected partition inequalities. An incoming directed cut is not the support of one such projected trace. Source extraction thm:extraction similarly uses maximal undirected packing partitions, not rooted directed separators.

Simply replacing an undirected packing by a packing of out-arborescences is unjustified. Even adding the canonical head frame and retaining ALL its cross blocks does not repair that implication: frame-obstruction.md constructs an infinite family satisfying errors smaller than the source scale while losing every incoming arc of one large set. It exhibits bad matrix-certified outcomes, not the nonexistence of a good outcome.

## 2. First attempted repair: head constraints and graphic ranks

An out-arborescence is a common basis of the graphic matroid (on underlying arcs) and the head partition matroid (one incoming arc at each nonroot vertex, none at root). This statement itself is elementary: a graphic basis with these indegrees has n-1 edges and is a tree, whose unique paths from the root necessarily point outward. The representation does not turn common-basis preservation into two separate rank assertions.

For B a union of r out-arborescences, every nonroot indegree equals r. A half-sized selection with EXACT indegree q at every nonroot vertex and exactly q(n-1) arcs, whose whole arc set decomposes into q undirected spanning trees, would contain q out-arborescences by the classical directed packing criterion: for S avoiding the root,

 |delta_A^-(S)| = q|S|-|A[S]| >=q,

since each of the q undirected trees has at most |S|-1 internal edges. Exact forest-union membership is crucial. The source supplies existence of a large tree packing INSIDE a selected set, not an upper bound |A[S]|<=q(|S|-1) on every internal set of all retained arcs.

The attempted approximate version loses the scale. If head counts are at least (1/2-epsilon)r per vertex while a graphical upper trace bounds internal counts by (1/2+epsilon)r(|S|-1), subtraction yields only

 |delta_A^-(S)| >= r/2-epsilon*r*(2|S|-1).

For unbounded |S| this does not guarantee one incoming arc. The explicit full-stack obstruction proves the failure is not merely pessimistic bookkeeping.

Possible continuation: select directly in the common-basis/forest-union polytope while retaining all cut estimates, or impose lower bounds on all rooted incoming cuts during halving. No such dimension-independent selection is proved here. The general crossing-polymatroid rounding theorem in Bansal et al. gives 2b+Delta-1, where Delta is edge frequency among constrained sets. Applied to ALL vertex cuts Delta grows exponentially with n, so it cannot close T174D. Its factor-two integrality-gap example involves arbitrary additional edge sets, is not Eulerian, and does not disprove our target.

## 3. Second route: fractional Eulerian augmentation

Let l be the 0/1 arc indicator of the direction-retaining T0, and let alpha=C0/k. Define u=l+alpha*1_A(D). For every S,

 l(delta_D^-(S)) <= |delta_T0(S)| <=alpha |delta_D^+(S)| <= u(delta_D^+(S)).

Thus Hoffman's circulation criterion gives a real circulation f with l<=f<=u. This is the same augmentation operation actually used in Asadpour et al., SODA2010 Section6, Theorem6.2 and proof of Theorem6.1/Lemma6.1. It is credited, not a new bridge. In particular

 f(delta_D(S)) <= |delta_T0(S)|+alpha |delta_D(S)|
                <=3alpha |delta_D^+(S)|.

The real circulation has connected support because it contains T0, so its support is strongly connected. However the bound is on fractional mass, not the number of support arcs. Extracting an arbitrary out-arborescence from its support has no justified all-cut bound.

The source's simultaneous cost-and-cut corollary controls ONE cost functional along with undirected cuts. The primary ATSP proof obtains an integral minimum-cost circulation with the lower bound l and NO finite upper bounds. Its comparison f only bounds that one cost; it does not prove that the same integral circulation obeys u or all cut bounds. Taking each cut as a different cost gives different integral solutions and does not supply a simultaneous selection.

There is an exact integer obstruction to retaining these individual-arc upper bounds. Whenever alpha<1, any integer g with l<=g<=l+alpha must equal l on every arc. A nonempty orientation of an undirected tree cannot be a circulation: a leaf has precisely one nonzero incident tree arc, and therefore unequal incoming and outgoing flow. Hence these fractional intervals never contain an integer circulation. This is a general proof, not a numerical example. Rounding upper bounds upward permits one extra unit on every unused arc and loses the needed 1/k scale. It does not rule out a different rounding scheme controlled directly on cuts.

A minimax or randomized convex decomposition does not bypass the issue: small mean use of every edge does not imply existence of one output small on every cut. The source introduction already identifies that average-versus-simultaneous distinction for ordinary tree packings.

## 4. Exact remaining sufficient operation

A sufficient NEW step would operate on every finite digraph H with q>=q0 arc-disjoint out-arborescences rooted at the given root, without assuming H remains Eulerian. It would select a subgraph H' and a positive q' satisfying

 q/4<=q'<=q/2,
 H' contains q' arc-disjoint rooted out-arborescences,
 |delta_H'(S)|<=a_q |delta_H(S)| for every S,
 a_q/(q'/q)<=1+C1 q^(-eta),

for absolute q0,C1 and eta>0. The ordinary directed packing theorem would supply q=k initially. Geometric decrease gives sum q_i^(-eta)<=q0^(-eta)/(1-2^(-eta)), so the source's already-paid product argument yields O(1/k) total-cut control and a final out-arborescence. This is a precise sufficient lemma, NOT an assumed theorem and NOT a conditional nomination. No such step is established.

Alternatively one could keep Eulerian balance through all selected stages with summably small relative losses and then use directed reachability. The source's independent-vector selections do not enforce exact flow balance, and its one-cost circulation augmentation does not preserve simultaneous cut bounds. No balancing construction with the required scale was found.

The full target remains unresolved at every original quantifier. Neither a logarithmic loss, symmetric host, adjustable root, finite instance, nor the auxiliary failure theorem is substituted for it.
