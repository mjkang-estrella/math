# Family 089: planar and bounded-treewidth L1 embeddings

This is a prefreeze feasibility note. Nothing in it is nominated.

## Stipulated source statements (read in full)

- Planar source, `sections/introduction.tex`, `thm:main`: there is a universal C>=1 such that every finite connected planar graph with positive real edge lengths embeds into L1 with d_G<=||f(x)-f(y)||_1<=C d_G.
- Treewidth source, `01-introduction.tex`, `thm:main`: for every k>=2 there is C_k such that every finite connected graph with a tree decomposition of bag size at most k embeds for every positive length function, with distortion C_k independent of the vertex count, decomposition depth and length ratios.
- Planar source, `sections/consequences.tex`, `cor:almost-embeddable`: fixed-parameter almost-embeddable families embed, through Lee–Sidiropoulos (STOC 2009) Theorem 1.7 and Lemmas 1.2 and 1.5. The source then states that it does not establish closure under clique sums of order greater than one and does not prove the full GNRS conjecture.

## What history already pays or stops

Analytic r17 (`status.json`: PRE_FREEZE_SCREEN_UNPAID, principal family 089) isolated the unpaid operation as a compatible cut-law reservoir for large planar bags with bounded clique interfaces. It recorded counterexamples to finite-particle replacement, K4-chain Markov gluing, cut-metric subtraction on a tight triangle and an L1-valued particle pigeonhole. Those are not repeated here. Analytic r114 only points back to r17. The r129 searches found no history work on the 2-sum-only route below (see `reading-limits.md`).

## Route tested in r129: the smallest class beyond both sources

Wagner's theorem describes the edge-maximal K_{3,3}-minor-free graphs as clique-sums of order at most two of planar graphs and copies of K5. A weighted subgraph metric is obtained by giving each deleted edge its distance in the subgraph, so it suffices to treat such sums. A 2-sum of planar graphs is planar. The 2-sum closure of {K5} alone has bounded treewidth. So each source covers one pure piece type, and the only missing ingredient is alternation between planar pieces and K5 pieces at unbounded depth. That makes this class the natural first test of the 2-sum step that r17 did not isolate.

Three elementary checks were made.

1. **Planar gadget replacement fails topologically.** Suppose each K5 node of the decomposition is replaced by a planar gadget on the same five terminals, so that the planar source applies to the whole graph. If all ten terminal pairs carry attached pieces that each contain a path between the pair, those ten paths are internally disjoint from each other and from the gadget. The result contains a subdivision of K5, so it is not planar. Distance-faithful gadgets therefore cannot make the whole graph planar in general.

2. **Stochastic planarization is ruled out by a cited theorem.** The abstract of Chakrabarti–Jaffe–Lee–Vincent (FOCS 2008) states: if Q and H are minor-closed and Q is closed under 2-sums, then members of Q embed non-trivially into non-contracting distributions over members of H only if Q is contained in H. K_{3,3} is 3-connected, so the class of K_{3,3}-minor-free graphs is minor-closed and closed under 2-sums. It contains K5, which is not planar. So there is no nontrivial random planarization to which the planar source could be applied. Only the abstract was read; the full statement and its quantifiers were not checked against the paper body.

3. **The remaining step is the 2-sum gluing theorem for an infinite family.** Lee–Poore (SoCG 2013) prove the Lee–Sidiropoulos 2-sum conjecture for every FINITE family, and characterize the distortion of a 2-sum closure through constrained embeddings of its members (abstract). Planar graphs together with K5 form an infinite family. The handbook chapter by Indyk, Matoušek and Sidiropoulos (3rd ed., ch. 8) likewise says that the k-sum conjecture is verified only for edge-sums over graphs of bounded size. Applying the Lee–Poore characterization would need a constrained embedding of every planar graph, which neither source provides. The Lee–Poore body could not be obtained (ACM PDF 403; a guessed author URL 404), so its exact constrained-embedding condition was not read.

## Why this stops

The missing operation is the gluing theorem itself: uniform control of L1 distortion under unbounded-depth 2-sums of an infinite family. The brief directs rounds away from wholly unbuilt famous central invariants, and this is a special case of the open 2-sum conjecture. No closable unpaid compatibility was found between the two sources. The depth-compounding distortion under naive per-level gluing was not carried to a proof or a lower bound. No target was frozen. No claim is made about the literature status of the K_{3,3}-minor-free case beyond the statements read.
