# Caro–Tuza parity orderings: partial structural progress

No full source endpoint is established. Source is workshop 2411.10046v1, §7 p10; the longer primary 2408.04257v1 gives Definitions 3.10–3.11 and Problems 6.12–6.13. All graphs below are finite simple graphs. An A-order has earlier-neighbor degree zero or odd at every vertex. A B-order also permits positive even earlier degree if later degree is zero. Recognition and construction in polynomial time are the actual target.

## Mechanism 1: reverse deletion and its obstruction

An A-order exists exactly when one can recursively remove a vertex of odd current degree or of degree zero. This follows by reversing an order: the current neighbors of the last remaining vertex are precisely its earlier neighbors. Conversely any successful deletion sequence reversed satisfies the defining condition. Thus this is an exact search rule, but arbitrary choices do not work.

The exact check finds a four-vertex witness with edges {02,12,03,23}. Deleting the smallest eligible vertex 1 leaves the triangle on {0,2,3}, where every degree is two, so that greedy branch fails. Yet order (0,1,3,2) has earlier degrees (0,0,1,3), hence is an A-order. Equivalently delete 2 first, leaving edge 03 and isolated vertex 1. This rejects the structural hypothesis of confluent greedy elimination; it is not merely a larger census.

## Mechanism 2: prescribed parity and independent source sets

Orient edges from earlier to later in an A-order and let S be its zero-indegree vertices. S is independent. Every vertex outside S has odd indegree, so counting edges gives

    |E| = sum indegree(v) ≡ |V| - |S| (mod 2).

The cycle 0–1–2–3–0 with leaf 4 adjacent to 0 admits order (1,2,3,4,0), with earlier degrees (0,1,1,0,3). It has five vertices and five edges, so any A-order must have an even number of sources. It cannot be dual-critical, which requires a unique source and odd indegrees everywhere else. Thus A-order recognition is not simply dual-criticality of G.

There is nevertheless an exact source-set reduction. For an independent S⊆V, let R=V\S and build H_S by retaining G[R], adding one new vertex r, and joining r to v∈R exactly when |N_G(v)∩S| is odd. Then

    G has an A-order ⇔ H_S is dual-critical for some independent S.

Proof, forward: choose S to be the source set. All edges incident with S point away from it. On R, the required indegree parity is 1-|N(v)∩S| modulo two. Hence it is odd precisely on T={v∈R: |N(v)∩S| is even}. Király–Kisfaludi-Bak, 1410.1653v1 Proposition 9 (p3), constructs exactly H_S for this T and proves the equivalence to dual-criticality. The body of its proof uses Theorem 3 to choose the new vertex as unique source.

Reverse: take a prescribed-parity acyclic orientation on G[R] supplied by Proposition 9. Orient all edges from S toward R; independence of S makes the resulting orientation acyclic. Every vertex of S has indegree zero; every vertex outside S has odd total indegree and thus positive indegree. A topological order is an A-order. This also covers an edgeless G by S=V and the one-vertex dual-critical graph H_S. Empty G is separately trivial.

The exact reduction is elementary once Proposition 9 is available. It is not offered as a substantive new theorem or as resolution of the source. Enumerating independent S is exponential. The source's §4 explains the randomized polynomial method for fixed dual-criticality; that does not compress the existential source-set search or derandomize it.

## What the checks establish

checks.py independently compares subset dynamic programming with brute permutation verification on all 1,099 labeled simple graphs of orders 1 through 5, checks the source-parity identity, and compares A-recognition with the independent-source-set reduction. The purpose is to validate the reduction and certify the two shortcut counterexamples. The mathematical arguments above do not rely on the finite range for their universal validity.

The subset recursion extends a prefix X by v if |N(v)∩X| is zero or odd. For B, it also accepts even degree when N(v)\(X∪{v}) is empty. It takes O(n 2^n) states/transitions up to bit operations, and yields a witness order; it is not polynomial in n.

## Exact residual gaps

1. Compress the search over independent source sets S into a deterministic polynomial algorithm, or establish the appropriate computational hardness. No claim of either is made.
2. Resolve the full Type B recognition/construction question; the exact exponential verifier is not its solution.
3. Inspect closer later primary results on these ordering notions and on generalized dual-criticality. The bounded arXiv searches are noisy; absence of a found successor is not clearance.
4. A fresh current public-registry head was not fetched because the inherited GitHub routes are barred. Immutable cache screening supplies a duplicate exclusion, not current novelty certification.

No PROOF.md is produced because no full literal endpoint has been proved or refuted.
