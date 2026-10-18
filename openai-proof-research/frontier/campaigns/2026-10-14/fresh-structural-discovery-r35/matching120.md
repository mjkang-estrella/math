# Family 120: weighted optimum preservation is unpaid

## Full screened target

Input: any finite simple undirected graph, explicitly encoded, with arbitrary **signed binary integer** edge weights. Write L for the complete input bitlength; a weight can have up to L bits. Objective: an exact maximum-total-weight matching, with no requirement to maximize cardinality or be perfect. Empty matching is allowed. The proposed target was a uniform randomized algorithm on a logarithmic-word RAM with word size Θ(log(L+2)), with multiword arithmetic, random-bit generation, and output charged, taking L^{1+o(1)} bit-equivalent work on every path, always outputting a valid matching and attaining the optimum with probability at least 2/3. Equivalently the claimed time must be O_eta((L+2)^{1+eta}) for every fixed eta>0 with a uniform specified algorithm, not unit-cost arithmetic on arbitrary weight words. This is a **screened objective, not a theorem**.

Signed weights cause no conceptual obstruction: negative-weight edges can be deleted for this unconstrained-cardinality objective. That observation does not pay the algorithm. Restricting weights to polynomial magnitude, perfect matchings, bipartite graphs, or an easier rank regime is not a rescue of this target.

The pinned source's `01-introduction.tex` and `02-preliminaries.tex` give an exact **cardinality** result on a word RAM in terms of n+m. `03-matching-state.tex` uses rows assigned injectively to bins, factor-critical expansions, a captive-row deficit h(X), and minimal tight sets with h=1. These are feasibility/cardinality certificates. The stored exposure matching has no weight-sensitive dual certificate. `10-f-factors.tex` concerns ordinary edge subsets of prescribed degree, not binary multiplicities or weighted optimization.

## Explicit contraction barrier

Vertices are a0,a1,a2,b0,b1,b2,u0,...,u5. Put triangles on a0,a1,a2 and on b0,b1,b2, a cycle u0u1...u5u0, and rungs ai-ui and bi-u(i+3), i=0,1,2. All cycle/triangle edges have weight zero and all six rungs have weight W>0. This graph is simple and cubic.

The six rungs form a perfect matching of weight 6W. No matching has greater weight, and a weight-6W matching must contain all six rungs. If each triangle is represented by a single odd bin that can have exactly one external matching edge, every lifted quotient perfect matching has only two rungs and weight 2W. A quotient perfect matching exists: use a0-u0, b0-u3, outer edges u1-u2,u4-u5, and internal edges a1-a2,b1-b2 on lifting.

This is compatible with the local **unweighted** tight-set geometry: begin with internal edges a0-a1,b0-b1 and a perfect matching of the outer cycle. The free a2 can create row a1 assigned to bin a0; its other bin neighbor is a2. The set of these two bins has one captive row and h=1, so contracting its row and bins yields the first triangle. Likewise for the second triangle. This describes a permissible local tight configuration; it does not assert that the source's globally prescribed execution necessarily chooses this sequence. Factor-criticality and feasible exposure alone are insufficient to preserve weighted optima.

`checks.py` exhaustively enumerates all matchings of this graph at W=1 and verifies the unrestricted optimum 6 and the best perfect matching with one external rung per triangle 2. Multiplying by W gives the symbolic example.

## Actual primary operation comparison

Duan–Pettie–Su, [Scaling Algorithms for Weighted Matching in General Graphs](https://arxiv.org/abs/1411.1919), §2.1 Properties 1–2 and Lemmas 2.1–2.2, attaches vertex and odd-set duals to blossoms. Domination plus tight matching/blossom edges certifies optimality; relaxed inequalities give an additive error later removed by scaling. The scaling algorithm's Figure 5 changes weights and duals together and liquidates blossoms. This is the weight-sensitive operation missing from the cardinality-only transfer. Merely calling an unweighted engine inside scaling supplies neither these invariants nor the advertised total bit bound. The primary paper was inspected at these operations, not completely re-proved or treated as a current-best survey.

A genuine extension would need a weighted contraction/repair invariant, including when to dissolve an odd bin, and an amortized implementation maintaining it within the full bit budget. The example does not prove that such an invariant cannot exist. No such invariant was obtained.
