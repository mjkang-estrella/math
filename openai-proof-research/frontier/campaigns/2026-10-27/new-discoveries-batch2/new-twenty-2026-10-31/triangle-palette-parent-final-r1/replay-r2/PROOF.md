# Candidate refutation of MathDB 364095

Target: Pilśniak–Woźniak, arXiv:2407.19050v1, Conjecture 5, page 4. For every n >= 4, the least number of edge colors of K_n giving distinct **sets** of colors on every pair of distinct triangles is conjectured to be n - 1.

Claim proved: no four-color edge coloring of K_5 distinguishes its ten triangles by sets. Therefore the conjectured equality fails at n = 5. This does not refute the separate multiset conjecture. No optimality assertion at larger orders is made.

Represent the ten edges in order 01, 02, 03, 04, 12, 13, 14, 23, 24, 34, with values a,b,c,d,e,f,g,h,i,j in {0,1,2,3}. The palettes are

{a,b,e}, {a,c,f}, {a,d,g}, {b,c,h}, {b,d,i},
{c,d,j}, {e,f,h}, {e,g,i}, {f,g,j}, {h,i,j}.

For a color x put b(x) = 2^x. The bitwise OR of b(x), b(y), b(z) is an exact encoding of the set {x,y,z}. This preserves repetitions correctly: repeated colors contribute one bit, not their multiplicities. `Palette.code_sound` proves the implication from equal encodings to equal Finsets for every six colors, using kernel `decide` over this finite domain.

The exhaustive checker assigns the edge colors in that order. After each assignment it tests all newly completed pairs of palettes. On a collision it returns true (this prefix cannot extend to a distinguishing coloring). Otherwise it branches over all four values of the next edge. At a fully assigned, collision-free leaf it returns false. Each stage is explicitly defined, without unbounded recursion, in Checker.lean. `Palette.check_pass` proves by kernel `decide` that the root returns true.

The soundness bridge is fully proved, rather than inferred from a successful computation. `Palette.all4_spec` establishes that a true conjunction of the four branch checks implies truth on any color in Fin 4. Suppose all 45 palette codes were unequal. `Palette.code_no` specializes each of these finite conjunctions to the proposed coloring and rewrites every collision branch using the appropriate inequality. It reaches a false leaf asserted equal to true, a contradiction. `Palette.no_four` then starts from injectivity of the actual triangle-to-Finset map. For each of the 45 pairs, `code_sound` and that injectivity force the two distinct triangles equal if their codes were equal. Hence all code inequalities hold, contradicting `code_no`.

The final definitions use actual unordered complete-graph edges, each represented once by a pair i < j, and actual triangles, represented once by i < j < k. A coloring is an arbitrary map from these edges to Fin k. `trianglePalette` takes the Finset of its three edge colors. `Achievable n k` says this map on triangles is injective. `SourceClaim` says n - 1 is the least achievable color count for every n >= 4, using Mathlib's `IsLeast`. Its membership component at n = 5 supplies precisely a distinguishing four-color coloring. `Palette.source_refutation : ¬ Palette.SourceClaim` applies `no_four` to contradict it. No finite sweep is substituted for an asymptotic or unlimited claim: one finite counterexample order logically refutes this universal statement.

An independent Python exhaustive search with no symmetry reduction supports the same finite obstruction, but it is not a trusted premise of the Lean proof. Its complete code and output are retained. It visits 1, 4, 16, 64, 256, 1024, 4096, 13824, 38208, 65856, 47616 nodes at depths 0 through 10. Collision prunes at depths 6 through 10 number 640, 4272, 21744, 53952, 47616; no valid leaf remains.

The strict replay, dependency pins and complete local declaration audit are in the proof packet and replay receipts. Independent statement-fidelity, prior-art, significance and root acceptance reviews are still required. This proof receives zero campaign credit here.
