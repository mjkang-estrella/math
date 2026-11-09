# 321500 — exact scope and sustained minimax route (zero credit)

Primary: https://arxiv.org/pdf/1104.5098v1, Section 4, Conjecture 4.3, Definitions 1.1–1.2. Saved PDF/text and SHA-256 are in evidence/fetch-log.json. The graph has n+1 levels, indexed i=1,...,n+1, with vertices (i,j), 1<=j<=i. Edges (i,j)->(i+1,j) and (i,j)->(i+1,j+1), for i<=n. The bottom level consists of sinks. Thus n is path length, not number of levels. The primary's N=n(n+1)/2 counts non-sinks, despite calling them vertices; total graph order is (n+1)(n+2)/2. Do not inherit that counting typo.

An input is an arbitrary assignment sigma of a left/right switch to EVERY non-sink, including vertices off the root path. A query asks one vertex's switch, not whether the vertex belongs to the path. A batch of at most k queries is chosen using answers of previous rounds only; switches are fixed throughout. Complexity is deterministic worst case over ALL assignments. The output is either the full selected root-to-bottom path or its bottom vertex. For ALL positive n,l, with k=l(l+1)/2, the conjecture says the minimum worst-case rounds for BOTH tasks are ceil(n/l). No randomized/expected complexity claim is involved.

The upper bound queries every non-sink in the next l-level subpyramid, then follows the revealed l edges and repeats at the new root; the final truncated subpyramid costs no more. This is already Claim 4.4, not a new proof. Its printed recursive n-values contain an evident arithmetic typo; the valid remaining height is n-l. Existing lower bound Theorem 4 is ceil(2n/(k+1)); it closes l=1,2, but for l>=3 is weaker than ceil(n/l). We do not promote these known cases or repairs.

## Exact full-scope minimax endpoint

Let U_n be the finite non-sink set. A history h is a partial map U_n -> {L,R}. Let C(h) be all its total extensions. Define terminal_path(h) iff all sigma in C(h) select the same path; terminal_sink(h) iff all select the same sink. For task t, define W_t(h,0)=terminal_t(h), and

W_t(h,r+1) iff there exists Q subset U_n\dom(h), |Q|<=k, such that for every a:Q->{L,R}, W_t(h union a,r).

This exactly describes deterministic round strategies by induction, since every answer vector is compatible with a total input. The missing universal lower bound is: for every positive n,l and natural r with r*l<n, NOT W_sink(empty,r). Together with Claim 4.4 and sink<=path this proves the exact claim. This is a viable Lean endpoint once the adversary lemma exists, but it has not been proved here.

A simplistic per-transcript assertion that a batch can never reveal more than l path edges is false: asking six vertices of a single root path can reveal six edges on the compatible transcript for k=6,l=3. A correct lower bound must select adversarial answers and control information saved off the eventual path across rounds.

## A concrete combinatorial adversary, beyond a sweep

For two rounds, fix first batch Q and answer vector a. Let R(Q,a) be the set of unqueried non-sinks reachable from the root by edges respecting a at queried vertices (both edges allowed elsewhere). The final path batch MUST include every vertex in R(Q,a): if v is omitted, choose a compatible root-to-v prefix, keep all other switches fixed, and vary only v. Both completions give the same query transcript and different paths. Conversely querying all of R suffices. Thus two-round path search is possible iff some Q of size <=k has max_a |R(Q,a)|<=k. This is an exact combinatorial reduction, not an unproved greedy approximation.

To get a sink adversary too, restrict a so that all queried vertices on a given row have the same answer d_i. Every reachable row is an interval [a,b]. If Q_i is the queried set on that row, the cost is b-a+1-|Q_i intersection [a,b]|. A left answer yields next interval [a,b+1-1_(b in Q_i)], and a right answer yields [a+1_(a in Q_i),b+1]. Therefore the exact maximum residual size under this restricted adversary is the DP

F(i,a,b)=b-a+1-|Q_i intersection [a,b]| + max(F(i+1,a,b+1-1_(b in Q_i)), F(i+1,a+1_(a in Q_i),b+1)),

with F(n,*,*)=0 in zero-based rows. This follows because the shift of the entire interval fills every interior position, leaving only the indicated boundary potentially absent. The row's answer can be chosen after Q; maximization recursively chooses its continuation.

For these uniform-row first answers, every v in R is essential to the sink function as well: choose a compatible prefix ending at v and assign all remaining switches, on each later row, the row's already fixed direction (arbitrary if unqueried). Paths from v's two children then remain one column apart all the way to the bottom. Holding every other switch fixed, varying only v gives different sinks and identical query answers if the last batch omits v. Thus the same |R| last-batch necessity holds for sink identification under this restricted adversary.

This provides a concrete route to an analytic two-round lower bound: prove a compression/isoperimetric inequality min_{|Q|<=s_l} F_Q(0,0,0)>s_l whenever n>2l. It is NOT proved here. Moreover, even such a theorem leaves arbitrary r unresolved: previously fixed nonuniform directions and information saved in several batches require a stronger invariant. No claim that the DP itself establishes the conjecture.

## Finite diagnostics and their precise limit

pyramid_two_round.py enumerates every size-6 first batch among 28 non-sinks at n=7 (376,740 batches). For each it maximizes R over all answer vectors, stopping a batch once it cannot improve the current best. Minimum maximum residual is 10, achieved by the six top-three-level vertices. pyramid_uniform.py independently optimizes the restricted uniform-row adversary with the interval recurrence; it also obtains 10. Thus both numerical procedures obstruct a two-round strategy in this one instance, consistent with the conjectured value 3. Monotonicity justifies checking exactly k queries: enlarging a first batch cannot increase its worst remaining uncertainty. These outputs are unformalized exact finite computations, not universal proofs and not separately creditable parameter results. The C++ source was drafted but could not run because g++/clang++/cc are absent; the reported numbers come only from Python.

No Lean project was started: the universal adversary, not certificate syntax, is the decisive missing mathematics. A full certificate would additionally need the strategy/recurrence equivalence, exact graph/input/output definitions, minima and ceiling arithmetic. No sorry/admit or claimed endpoint is present.

Actionable next work: prove or refute the displayed compression inequality symbolically, then test whether its potential can survive one more round with stored information. This is narrower and more informative than increasing unrestricted assignment sweeps. A single finite parameter proof earns zero discovery credit under this campaign.
