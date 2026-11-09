# MathDB 365710 — literal Lean proof map

This packet completes the ordinary argument in the assigned proof and the exact target in the source review. Namespace: `Sigma365710`. No unproved bridge is a hypothesis of the endpoint. The internal `HasCompleteBipartition` abbreviation is explicitly the existence of a set whose membership XOR equals adjacency; the public classification expands this into nonempty complementary independent parts with every cross edge present.

| Ordinary step | Lean declarations and files |
| --- | --- |
| Literal unordered all-pairs sigma_t, actual degrees, integer subtraction and square | `sigmaT`, Sigma/Basic.lean |
| Literal finite part objective | `F`, Sigma/Basic.lean |
| Actual graph K(a,n-a) on Fin n | `completeBipartite`, Sigma/Basic.lean |
| Positive parts give connectedness and triangle-freeness | `completeBipartite_connected`, `completeBipartite_cliqueFree`, Sigma/Basic.lean |
| A maximizing positive proper part exists | `exists_maximizing_part`, Sigma/Basic.lean |
| Unordered pair variance and handshake expansion | `pair_variance`, `sigmaT_degree_identity`, Sigma/Identity.lean |
| nm minus sum of squared degrees, with the inherited literal definition | `deficit`, `sigmaT_deficit_identity`, Sigma/Identity.lean |
| K(a,n-a) degrees, summation over its two parts and exact sigma_t formula | `completeBipartite_degree`, `sum_partition`, `completeBipartite_sigmaT`, Sigma/Attainment.lean |
| Local one-edge triple for every outside vertex of an induced P4 | `path_extension_witness`, Sigma/PathExtension.lean |
| P4-free triangle-free two-step endpoints have identical neighborhoods | `two_step_twins`, Sigma/Structure.lean |
| Connectivity propagates “neighbor of v or twin of v” along a walk; obtain the complete bipartition or an induced P4 | `completeBipartition_or_inducedP4`, `inducedP4_of_not_completeBipartition`, Sigma/Structure.lean |
| Adjacent endpoints have disjoint neighborhoods; count vertices adjacent to neither | `neither_count`, Sigma/DartDeficit.lean |
| Ordered-dart count is exactly twice the deficit; hence the deficit is nonnegative | `orderedDefect_eq_twice_deficit`, `deficit_nonneg`, Sigma/DartDeficit.lean |
| Actual finite subtype of ordered triples, and its cardinal equals the ordered-dart sum | `dartGood`, `card_dartGood`, Sigma/ConfigurationCount.lean |
| Double any family with injective vertex supports, using both edge orientations, without collisions | `deficit_ge_of_support_injection`, Sigma/ConfigurationCount.lean |
| Convert each local one-edge triple to a good ordered dart | `oneEdgeTriple_dart`, Sigma/Gap.lean |
| Inject the two seed supports {a,b,d}, {a,c,d}, plus one support for each of the n-4 outside vertices; all supports distinct | `inducedP4_deficit_gap`, Sigma/Gap.lean |
| Connected non-complete-bipartite triangle-free deficit is at least n-2 | `non_completeBipartition_deficit_gap`, Sigma/Gap.lean |
| Square-root-free discrete bracketing: use the least t with 8t(n-t) >= n^2, and select t or t-1 | `exists_bracketing_part`, Sigma/Bracketing.lean |
| Exact polynomial identity 16F = n^4 - (8a(n-a)-n^2)^2 | `F_square_identity`, Sigma/Bracketing.lean |
| General complete bipartition has positive proper size k and sigma_t = F(n,k), without relabeling assumptions | `sum_membership`, `bipartition_value`, Sigma/BipartitionValue.lean |
| An induced P4 forces n >= 4 | `non_completeBipartition_order`, Sigma/Endpoint.lean |
| Complete the square in the edge count and subtract n times the deficit. For n >= 7 combine with bracketing; for n=4,5,6 compare with the star | `non_completeBipartition_strict`, Sigma/Endpoint.lean |
| Universal domination for every maximizing a, with actual connected and CliqueFree 3 extremal graph | `extremal_completeBipartite`, Sigma/Endpoint.lean |
| Every connected triangle-free attainer is complete bipartite, with both independent parts nonempty | `attainer_classification`, Sigma/Endpoint.lean |
| Existential exact source endpoint | `mathdb_365710`, Sigma/Endpoint.lean |
| Singleton separately, with no two-positive-part claim | `sigmaT_singleton`, Sigma/Basic.lean |

The structural proof uses neighborhood twins and induction on an actual walk instead of the proposed boundary-edge argument. It requires no distance function, cograph theorem, or additional hypothesis. The ordered-dart identity avoids unordered triple quotient bookkeeping; unordered supports are used only to establish the explicit injection.

All four binding definitions, `sigmaT`, `F`, `completeBipartite`, and `deficit`, are unchanged from r1. Basic.lean, Identity.lean and PathExtension.lean are byte-identical copies. Attainment.lean changes only a stale documentation comment.

## Validation boundaries

NegativeControls.lean checks specific factor-of-two, subtraction, missing-chord, triangle-free, and balanced-part pitfalls by kernel reduction. scripts/rejections.py additionally requires the compiler to reject three explicit false mutations. These are finite controls, not a substitute for the unbounded proofs.

Audit.lean audits every declaration originating in all Sigma modules and NegativeControls, including generated declarations. It records module origin, full explicit type and raw expression, actual value presence, safety, partiality, and all transitive axioms. Audit.lean and PrintAxioms.lean are inspection drivers, not theorem dependencies. The whitelist is exactly propext, Classical.choice and Quot.sound.

No source fidelity or worldwide novelty claim is inferred from the kernel checks. The binding review's outstanding prior-art limitations remain outstanding. Root alone accepts the result; this packet assigns zero campaign credit.
