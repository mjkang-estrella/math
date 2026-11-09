# MathDB321500: symbolic attempts and the remaining full-scope gap

Status: PARK, zero credit. No conjecture proof or counterexample. No Lean endpoint.
Coordinates below are zero based: non-sinks (i,j), 0<=j<=i<n; children (i+1,j), (i+1,j+1). Let T_m=m(m+1)/2. The target is deterministic worst-case sink AND path rounds ceil(n/l) at k=T_l, for all positive n,l. Upper bounds and l=1,2 are already in the primary. Read actual cached arXiv1104.5098v1, Definitions 1.1–1.2 and Section 4, especially Conjecture 4.3, Claim 4.4 and both proofs of Theorem 4. The previous lane's recurrence and numerical n=7 diagnostic are not new results and were not rerun.

## 1. Symbolic compression calculation

Fix a first batch Q. For a vector of uniform-row answers d_i, let I_i=[a_i,b_i] be the compatible reachable row, w_i=b_i-a_i+1, and q_i=|Q_i intersect I_i|. Set e_i=1 if the selected boundary belongs to Q_i: the right boundary for a left answer, the left boundary for a right answer. The interval recurrence gives

w_0=1, w_(i+1)=w_i+1-e_i.

Thus, exactly, with N=T_n,

R_Q(d) = sum_(i<n)(w_i-q_i)
       = N - sum_(i<n) q_i - sum_(i<n)(n-1-i)e_i.

This separates queries that directly remove reachable vertices from the downstream compression they cause. For Q consisting of the first l full rows, every I_i on those rows is a singleton, q_i=e_i=1, and thereafter q_i=e_i=0. Hence R=T_(n-l), independently of d. Importantly sum q_i can be much smaller than |Q|: all other queried vertices are stored off the current reachable path.

The proposed two-round inequality is

|Q|<=T_l and n>2l ==> max_d R_Q(d)>T_l.

Equivalently, for every such Q one must find d with weighted removed area strictly less than T_n-T_l. The stronger plausible extremal inequality max_d R_Q(d)>=T_(n-l) would imply it. Neither inequality is proved here. Summing the elementary e_i<=1 and sum q_i<=|Q| is too weak: it loses the cost of forcing boundary hits at positions selected by earlier d's. This is the exact isoperimetric gap, not a bound supplied by the recurrence itself.

### A fixed averaging shortcut fails, symbolically

One might replace max_d by the average over independent fair row directions and try to prove the stronger extremal inequality that way. Take the SIX fixed queries

Q={(0,0),(1,0),(1,1),(2,1),(3,1),(3,2)}.

For n>=4, after four rows the expected residual already counted is 1 and the expected reachable width is 7/4. To see this without a search: if the first two directions differ (probability 1/2), the path reaches (2,1); whichever its answer, it then reaches a queried middle vertex on row 3, so initial residual is 0 and outgoing width 1. If the first two directions agree (probability 1/2), row 2 contributes one unqueried point, row 3 contributes one, and the outgoing width is 2 or 3 with equal probabilities. Thus E residual=1, E width=7/4. All later rows are unqueried, so

E R_Q = 1 + 7(n-4)/4 + (n-4)(n-5)/2
      = T_(n-3) + 1 - n/4.

For every n>4 this is smaller than T_(n-3). This refutes only the displayed fair-average surrogate. It does NOT refute max_d R>=T_(n-3), nor the weaker desired >T_3. In fact the worst direction for this Q gives initial residual 2 and outgoing width 3, much larger than the average. diagnostics.py checks the sixteen vectors for this single Q and the closed formula; no first-batch optimization sweep is part of the deliverable.

## 2. Arbitrary rounds: a legal but inadequate response policy

Freezing one direction for each row when that row is first touched is compatible with all earlier answers. It also makes every later queried vertex on that row receive that direction. This repairs compatibility but destroys the desired lower bound.

For EVERY k>=1 there is a two-round strategy against this response policy at height n=k+1:

Round 1: query (i,0) for i=0,...,k-1 and record d_i.
Let x_0=0 and x_(i+1)=x_i+d_i for i<k.
Round 2: query all (i,x_i) for 1<=i<k that were not already queried, and query (k,x_k).

The second batch has at most k vertices. Under the frozen-row policy its answers at rows below k agree with d_i, so the entire actual prefix is certified, and the final queried switch gives the sink. This is a fully specified strategy and a proof for the response policy, not an algorithm achieving two rounds on arbitrary input. On arbitrary answers, a newly queried candidate-path vertex might disagree with its row representative, invalidating the predicted continuation.

For k=T_l and l>=3, k+1>2l because k+1-2l=(l-1)(l-2)/2>0. Therefore this policy cannot establish the target even at height k+1. No potential valid for every transcript of that policy can repair the problem. This is an arbitrary-parameter obstruction, not a numerical n=7 lower-bound diagnostic.

## 3. Sink indistinguishability: a stronger compatible adversary class

For arbitrary histories, unresolved path need not imply unresolved sink. At n=2 fix h(1,0)=R and h(1,1)=L, leaving the root unknown. Both choices at the root lead to sink (2,1). The path is unknown, but the sink is determined. A potential measuring merely the length of the known path prefix cannot characterize sink termination.

A useful alternative is ROW-MONOTONE partial histories. On each row forbid an answered R strictly to the left of an answered L. Equivalently, each row's answered switches extend to a threshold assignment L for j<t and R for j>=t. These histories may be nonuniform. They extend legally across arbitrary rounds: keep a threshold interval for each row and answer each new query using any threshold in that interval, narrowing the interval if needed. Every finite consistent history extends to a fixed total input; adversarial timing does not require switches to change.

Here is a rigorous ordinary-mathematical sink bridge for this class. If h is row-monotone and v is an unqueried reachable non-sink, choose a compatible prefix ending at v. On every row strictly below v, complete switches by any monotone threshold extending h. Such a row map j |-> j+1_(j>=t) is strictly increasing on integer columns. Hence two paths starting at v's different children stay at different columns under all the later threshold maps. Complete all remaining switches arbitrarily consistent with h and the chosen prefix, and form two inputs differing only at v. They have the same history and different sinks.

Notice the prefix need not itself be monotone: only one vertex per earlier row is used and it merely needs to respect h. We do not claim the two final total inputs are row-monotone, which is unnecessary: the task's input space allows all switch assignments. Monotonicity is used only for the common suffix completion, where it ensures noncoalescence.

Consequences:

* For row-monotone h, sink termination is equivalent to path termination: if there is an unqueried reachable vertex the construction gives different sinks; if none, the unique root path is completely queried.
* For such h, a final nonadaptive batch must contain every unqueried reachable vertex. If it omits v, the two inputs just constructed agree on the whole batch and have different sinks. Conversely querying all reachable unknown vertices suffices. Thus the last-batch criterion is exact for sinks as well as paths, without pretending the two tasks coincide on arbitrary histories.

This class avoids the frozen-row attack because later answers can legitimately differ from a representative while respecting the threshold order. However the interval DP no longer applies. Even a full row [a,b] with an L at j and an R at j+1 can have a hole in the next reachable set. For example row 1 with L at 0 and R at 1 sends {0,1} to {0,2}. These histories are row-monotone, but the reachable set is not an interval. Replacing it by its convex hull invents a reachable point, and can overstate the sink uncertainty or the necessary last batch.

The exact update for a reachable set S is the union of the selected child of every queried vertex in S and BOTH children of every unqueried vertex in S. This set-valued update preserves all stored queries; its description does not supply the missing amortized inequality.

## 4. Other full-scope routes examined and why they stop

The primary's reverse-height response scheme with all off-prefix answers left charges two previously queried disjoint rails for each extra edge beyond the one new frontier query in a round. Merely replacing its factor two by a triangular charge is unjustified. Two parallel known leftward rails can be made as long as desired with only two vertices per row; choosing the shorter continuation at their parent witnesses two copies, not a cone containing 1+2+...+d vertices. Charging older queries more than once is the precise danger. The primary proves only 2n-r<=rk this way, which is its known Theorem 4.

A potential based only on remaining sink diameter or known prefix length omits stored row constraints. A row-uniform potential is insufficient by Section 2. A threshold-based potential survives the sink fidelity objection but needs the full reachable set, its gaps, and the previously queried vertices/threshold intervals. No per-batch l-progress assertion was used: favorable transcripts can reveal k path edges, so any proof must choose answers and account for credit accumulated in earlier rounds.

A genuine fast strategy was considered by certifying the predicted path after probing row representatives (Section 2). It succeeds exactly on frozen-row transcripts. It is not a universal counterexample because nonuniform replies can invalidate its predicted suffix inside its last batch. No full-input strategy beating ceil(n/l) was found. No claim of impossibility of a different strategy is made.

## 5. Exact next lemma, and what is still absent

The original uniform-first-batch weighted-area inequality in Section 1 remains a concrete analytic lemma, but even proving it would settle only two rounds. A promising next arbitrary-round test is to establish or refute the following stronger restricted-adversary assertion:

For positive n,l and r*l<n, every deterministic r-round strategy of batch size T_l has a transcript whose history remains row-monotone after each batch and still has an unqueried reachable non-sink after its final batch.

The sink bridge above would convert that assertion into actual sink indistinguishability. The assertion is NOT proved here and could fail for this response class; it is a testable strengthening, not a substitute assumption in an endpoint theorem. A successful potential would need to track stored queries and reachable-set holes; the old interval state cannot support it. Alternatively construct a full-input strategy defeating the universal statement, not merely a particular adversary policy.

No viable completed full-scope route survives these attempts in this session. The target is parked with this explicit obstruction and next lemma. There is no Lean project, custom axiom, theorem assuming an adversary lemma, axiom audit or clean rebuild represented as achieved. All helpers and diagnostics earn zero discovery credit.
