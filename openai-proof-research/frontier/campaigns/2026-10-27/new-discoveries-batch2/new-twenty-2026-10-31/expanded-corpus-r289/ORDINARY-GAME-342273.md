# MathDB 342273 — complete ordinary refutation, unqualified HOLD

Zero credit. No execution requested. The journal body and full citing/correction coverage are not cleared. A complete classical fractional-matching bridge below creates a substantive exclusion objection; root must adjudicate it before any investment. This is not CANDIDATE.md.

## Literal source and definitions

Lidbetter–Lin, arXiv:1903.12231 v1 and v2, Section 1, Proposition 14 (including its proof) and Conjecture 15. Both versions explicitly quantify arbitrary hypergraphs; neither requires connectedness or closure under subsets. A box has nonnegative reward, k is between 1 and n−1, the Hider chooses exactly k boxes, the Searcher chooses one listed hyperedge. Payoff is the sum of rewards in that hyperedge if disjoint from traps, otherwise zero. Reward means a sum over vertices, not arbitrary independently assigned hyperedge weights. All our vertex rewards equal 1 and are strictly positive. The complete-hypergraph k=1 theorem cannot be applied to this restricted strategy family.

## Exact finite object and full proof

Use five boxes {1,2,3,4,5}, one trap, unit rewards, and the five 2-element hyperedges
A={1,2}, B={2,3}, C={3,1}, D={1,4}, E={4,5}.
This is even a connected simple graph. Each allowable hyperedge has reward 2.

Give probabilities (1/5,1/5,1/5,0,2/5) to (A,B,C,D,E). Each vertex belongs to chosen hyperedges with total probability 2/5. For a trap at any of the five boxes the expected reward is therefore 2(1−2/5)=6/5.

For every probability vector on these five edges, summing its five vertex-incidence probabilities counts each selected edge twice and equals 2. Some vertex has incidence probability at least 2/5. Placing the trap there gives expected reward at most 6/5. Thus the strategy above is optimal and the game value is exactly 6/5. No minimax existence theorem is necessary.

An inverse-reward strategy has a nonempty support T and constant probability on T, because all rewards are 2. Let t=|T|, and let Δ(T) be the maximum vertex degree in its support graph. Its guaranteed payoff is exactly 2(1−Δ(T)/t).

If t=1 or t=2, Δ(T)≥1 and Δ(T)/t≥1/2. If t=3 or t=4, then Δ(T)≥2: otherwise the selected edges would be a matching, but a matching of 3 edges would require 6 distinct vertices. Hence Δ(T)/t≥1/2. If t=5, the support is all five edges and vertex 1 has degree 3, so Δ(T)/t≥3/5. In every case the payoff is at most 1, strictly less than 6/5. A support {A,E} attains 1, so the bound on inverse-reward strategies is sharp. This proves the exact negation of Conjecture 15 and the literal MathDB assertion for an interior allowed k, positive rewards, and connected allowable hypergraph.

The initially found disconnected triangle plus an edge is the same mechanism. Adding D makes connectedness explicit without altering the optimum. This is not a second outcome.

## Classical bridge and exclusion objection

For any nonempty finite simple allowable graph with unit vertex rewards and k=1, write p_e for the edge probabilities and M=max_v Σ_{e∋v}p_e. The guaranteed payoff is 2(1−M). Let ν* be the maximum fractional matching size, defined by x_e≥0 and Σ_{e∋v}x_e≤1. From any p, x_e=p_e/M is feasible with size 1/M, so M≥1/ν*. Conversely any optimal fractional matching x of size ν* normalizes to p_e=x_e/ν*, giving M≤1/ν*. Thus the game value is 2(1−1/ν*).

Here ν*=5/2 follows from the universal sum-of-vertex-capacities bound 2Σx_e≤5 and the classical triangle-half-weights plus disjoint-edge weight-one construction. The added bridge has weight zero. The complete failure of inverse strategies is exactly the elementary fact that no support subgraph has degree ratio ≤2/5. This is a complete routine classical bridge, rather than an argument that small size or ease alone makes the result ineligible. Recommendation: exclude from significant-discovery credit under that rule unless root identifies a substantive distinction. No inspected earlier paper was found printing this exact five-box witness; that is not proof of novelty, and the journal/citing gaps remain regardless.

## Dormant exact semantic Pi plan — NOT AUTHORIZED

Only if root separately clears source and significance: define a finite hypergraph as Finset (Finset (Fin 5)), the five sets explicitly, vertex rewards Fin 5 → ℝ identically 1, k=1, Hider actions as all subsets of cardinality 1, and Searcher strategies as real vectors indexed by the actual five hyperedges with nonnegativity and sum 1. Define reward as the vertex sum and expected payoff by finite sums with actual disjointness. Define optimality by comparison of the worst payoff (or universally against all trap actions, with an explicit minimizing action). Define inverseReward by ∃c>0, ∀e, p e=0 ∨ p e=c/reward e. Prove equal positive rewards imply uniformity on the positive support. Prove support cardinal t∈{1,…,5} and the degree counting lemma above; no generic solver, certificate search, or proxy game.

Endpoint: there exists this admissible instance with an optimal ordinary strategy, and no inverseReward strategy is optimal; therefore the universal source claim is false. Bridges include exact correspondence of index edges to Finsets, singleton trap enumeration, reward=2, sum of incidences=2, disjointness payoff identity, positive support normalization, matching bound, and the strict 1<6/5 comparison. Fixed five-action arithmetic and finite set identities suffice. No Lean run, implementation or solver was performed. Any later Lean audit must allow only propext, Classical.choice, Quot.sound.
