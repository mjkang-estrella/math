# 342387: ordinary refutation of the specified internal semidirect product

Status: full ordinary candidate, ZERO CREDIT. Not independently reviewed or formalized. Source-version/prior gates HOLD; no dispatch authorized. This is a refutation of the actual internal factorization, not a claim that the automorphism group has no abstract semidirect decomposition.

## Exact target and source
The complete literal object is records/342387.jsonl, with immutable provenance in provenance.json. Kovič, Pisanski, Zemljič and Žitnik, The Sierpiński product of graphs, arXiv:1904.04180v1 (8 April 2019), pp.9–16: Definition 3.2, Propositions 3.5, 3.6, 3.14, Theorem 3.17, and Conjecture 3.28. The target quantifies over connected graphs G,H on the same vertex set and all bijections f and asserts tilde A = bar A semidirect hat B. Here bar A consists of the admissible diagonal maps (g,h) -> (alpha(g), f alpha f^{-1}(h)). The generators of hat B fix the first coordinate and act on one fiber by an automorphism fixing f(N_G(g)) pointwise. These definitions were read from actual primary text, not search snippets.

## Explicit witness
Let V={1,2,3,4,5,6}, A={1,3,5}, B={2,4,6}. Let G be the complete bipartite graph with parts A,B. Let H be the simple cycle with cyclic order 1,2,3,4,5,6,1. Let f=id. Both graphs are connected (indeed 2-connected, though only connectedness is required here). Any two vertices of G in opposite parts are adjacent; two in the same part are joined through any vertex of the other part. The cyclic order explicitly supplies paths in H. Thus all target hypotheses are met.

Put r=(1 3 5)(2 4 6), the two-step rotation of H, and alpha=(2 4 6), fixing A pointwise. Alpha is an automorphism of G since it preserves both parts. It is NOT an automorphism of H: {1,2} is an edge, but its image {1,4} is not.

For g in A put beta_g=r, and for g in B put beta_g=id. Each beta_g is an automorphism of H. Define
  gamma(g,h)=(alpha(g), beta_g(h)).
This is a bijection: alpha preserves each part, and within each fiber beta_g is bijective, so the inverse on fiber alpha(g) is beta_g^{-1} followed by first-coordinate alpha^{-1}.

The Sierpiński product K=G tensor_id H has two edge types. Inner edges are {(g,h),(g,h')} for hh' in E(H); gamma preserves these because beta_g is an H-automorphism. Connecting edges have the form {(a,b),(b,a)} with a in A,b in B. Their images are {(a,r(b)),(alpha(b),a)}. Since alpha(b)=r(b), this is precisely the connecting edge indexed by {a,r(b)} in G. This correspondence is bijective on connecting edges, with inverse using r^{-1}. It is also bijective on inner edges. Thus gamma is a graph automorphism and respects the fundamental partition. Hence gamma belongs to tilde A.

## Obstruction to the factorization
Every element of hat B fixes every fiber setwise, so has trivial first-coordinate action. Every admissible diagonal d in bar A has form (g,h)->(delta(g),delta(h)), with delta in Aut(G) intersect Aut(H): preservation of inner H-edges forces delta in Aut(H), and the first-coordinate permutation is delta in Aut(G). Conversely these conditions suffice by direct inspection of the two edge types.

If gamma=d b for d in bar A,b in hat B, comparison of first coordinates forces delta=alpha. This contradicts alpha not in Aut(H). The same contradiction applies to b d. Therefore gamma is outside bar A hat B. In particular tilde A is not the asserted internal semidirect product. A single admissible example refutes the universal conjecture in its full scope.

A second independent obstruction strengthens the witness: hat B is actually trivial. For g in A, N_G(g)=B. An automorphism of C6 fixing 2,4,6 fixes 1,3,5 as well: 1 is the unique common neighbor of 2 and 6, 3 of 2 and 4, and 5 of 4 and 6. For g in B use the corresponding common-neighbor argument on A. All fiber stabilizers in the definition are therefore trivial. Every generator of hat B is the identity. Gamma cannot be diagonal because its H-action is r on A-fibers and id on B-fibers. This gives a direct failure even when the proposed kernel factor is trivial.

## Sustained checks, contrary assessment, and limits
The initial splitting shortcut was invalid: a projection of tilde A into Aut(G) is a homomorphism with kernel hat B, but an arbitrary liftable alpha need not have a diagonal lift. Proposition 3.5 imposes agreement only on N_G(g) separately for each g. The witness exploits exactly that gap. The special source theorem G=H and f an automorphism does not apply: our G has degree 3 and H degree 2. They are not even isomorphic. Relabeling via f=id does not repair this hypothesis. The source's example 3.11 has G=K3 and H=K3,3, so neither the same vertex set nor bijective f; it does not itself refute this target. The witness is not the previously credited flat K3,3 balance problem 352972: its target, graph product, quantifiers and obstruction are different. Shared graph notation alone supplies no duplicate bridge.

No finite search, enumeration, numerical experiment, CAS, solver, Lean, compiler or mathematical program was run. All calculations above are ordinary reasoning. No mathematical lemma remains unpaid in this ordinary refutation. Formal fidelity, source final-version comparison, bounded literature qualification, significance and independent adversarial assessment remain unpaid gates.

## Current public and version bounds
Three native search calls/nine queries are preserved in the exact plans/responses and search-budget.json. They exposed the original paper and a later journal reproduction; no applicable disproof body was established. Absence of hits proves no novelty. The guarded current arXiv page lists only v1. The later journal reproduction attempted at https://scispace.com/pdf/the-sierpinski-product-of-graphs-1r0hy4x9.pdf returned 403. It and alternate deliveries of that final body are unavailable; no retry was made. The journal search extract shows changed theorem numbering (3.19 rather than Proposition 3.19), so treating arXiv as a verified identical final version would be unjustified. Precise HOLD: compare the final published definition of bar A and the retained/revised counterpart of Conjecture 3.28; a broader bar A definition could change statement fidelity. This is not an assertion that a contrary final theorem exists.

Current four public registry roots were saved with observed heads in registry-inventory.json. Root HTML and filenames do not clear theorem bodies, and no worldwide clearance is claimed. Before any execution or acceptance the root must commission independent source/prior/significance review within applicable access rules. This lane supplies a reviewable ordinary proof and dormant plan only.
