# MathDB 360905 — orientable total domination interpolation

Verdict: full ordinary proof and literal general Lean endpoint, pending independent fidelity, prior-art, significance and root acceptance. Zero accepted credit is claimed. Credit risk is material: the proof is elementary and short; it may be judged a routine interpolation observation under the campaign standard. No available result was used as a black-box bridge, and it is not an augmentation of a printed graph construction.

## Source and exact statement

Anderson–Dravec–Johnston–Kuenzel, arXiv:2311.16307v1, Conjecture 3.1, attributes the conjecture to Hansen–Lai–Yue. Their original paper, JCMCC 29 (1999), 159–181, was retrieved. Pages 179–181 were read as rendered scans: Theorem 14 proves the complete-graph case by vertex deletion; the final conjecture on page 181 asks the general statement. The present proof uses neither that vertex-deletion method nor the complete-bipartite construction in the 2023 paper.

For any finite graph G admitting an orientation of positive indegree at every vertex, let dom_t(G) and DOM_t(G) be the minimum and maximum total domination number over those orientations. Every integer c between these extrema is attained by a valid orientation. A set S totally dominates D when every vertex, including members of S, has an incoming neighbor in S.

## Full proof

Fix valid orientations D and E of the same finite simple graph. Let Δ(D,E) be the set of arcs of D reversed in E.

**Forced-head lemma.** Suppose every arc a→b in Δ(D,E) is the unique incoming arc at b in D. Then every total dominating set S of D also totally dominates E.

First, every head v of an arc a→v in Δ belongs to S. Choose an incoming arc w→v in E, which exists by validity. This cannot be an arc of D: otherwise uniqueness forces w=a, contradicting that a→v was reversed. Consequently v→w is in Δ. Since this is the unique incoming arc at w in D, domination of w forces v∈S. Now consider any vertex v and an incoming neighbor a∈S in D. If a→v remains in E, v is dominated. Otherwise choose w→v in E. Again v→w is in Δ, so w is a head of Δ and hence belongs to S by the preceding argument. Thus v is dominated in E.

**Safe flip.** If S totally dominates D but not E, the contrapositive of the lemma supplies a→b in Δ and another incoming arc w→b in D with w≠a. Reverse a→b, obtaining F. The only vertex losing an incoming arc is b, which retains w→b, so F is valid. All other vertices retain their incoming neighbors. The set S∪{w} totally dominates F. Therefore γ_t(F)≤|S|+1. Also |Δ(F,E)|=|Δ(D,E)|−1.

Let D and E attain the lower and upper extrema, respectively, and fix c in between. More generally prove the assertion whenever γ_t(D)≤c≤γ_t(E), by strong induction on |Δ(D,E)|. If γ_t(D)=c, stop. Otherwise choose a minimum total dominating set S of D. It cannot dominate E, since |S|<c≤γ_t(E). The safe flip produces a valid F with γ_t(F)≤γ_t(D)+1≤c and smaller disagreement with E. Apply induction to F,E. This completes the proof, including disconnected graphs. Finiteness guarantees attained minima and maxima.

## Lean semantics

lean/Interpolation.lean encodes arbitrary finite vertex types and Boolean adjacency relations. Arc is equality to true; Asym prohibits opposite arcs and loops. Same equates the underlying undirected supports. TD is literally incoming domination of every vertex. Minimum is a dominating set whose cardinality is no larger than every dominating set. OrientationOf G D equates its support to G. spectrum G is the finite set of all attained minimum cardinalities; lower and upper are its actual min' and max'. Nonemptiness is exactly admissibility of a valid orientation, as proved by minimum_exists. No arbitrary invariant or assumed connectivity predicate is substituted.

Conjecture quantifies all finite vertex types, all underlying adjacency relations, every nonempty orientation spectrum, and every c between the extrema. The endpoint conjecture_true proves Conjecture. It even handles all Boolean supports admitting an asymmetric orientation, which necessarily are symmetric and loopless. The auxiliary interpolation theorem directly quantifies any two valid orientations and their actual minimum sets.

## Checks and remaining review

All connected labeled graphs of orders 3,4,5,6 were searched through all valid orientations: 1,22,603,25408 graphs and 2,122,16168,5545668 valid orientations. Their spectra have no gaps. This is only diagnostic; the Lean theorem is general.

The strict compiler and fresh extracted replay pass with axiom closure propext, Classical.choice, Quot.sound. The packet uses pinned Lean 4.34.1 and cached mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. No full upstream rebuild is claimed. All errors and resource failures remain in logs. Independent review is not performed by this lane and is still required.

Bounded prior-art screen: current Lean Pool projects and all candidates files; eight spaced GitHub repository queries; current Omega D5/Problems paths; OpenAI preprint paths at unchanged HEAD; primary 1999, 2023 and 2024/2026 domination papers. No matching general proof was identified in this scope. This does not establish global novelty. The 1999 complete-graph proof and 2023 complete-bipartite proof do not supply the forced-head lemma as a printed ingredient. The later Blázsik–Nagy paper concerns DOM_t=n−1, not general interpolation; the 2026 journal version was downloaded and its introductory definitions, Theorem 1.3 and relevant unique-in-neighbor proof cases were also inspected. No general interpolation theorem was identified there.
