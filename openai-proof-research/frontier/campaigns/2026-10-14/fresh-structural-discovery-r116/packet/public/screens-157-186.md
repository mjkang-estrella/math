# Two operative screens with historical antecedents

These are no-freeze examinations, not nominated results. All statements of the pinned OpenAI manuscripts, including proof operations, are stipulated true.

## 157: list coloring to correspondence coloring

The positive source is *A linear list-coloring bound in terms of the Hadwiger number*, pinned introduction `thm:main`, preliminaries, and the complete list-transfer section. The latter includes `list:constrained-coloring`, `lem:list-extraction`, `list:high-neighbor-count`, and `lem:additive-deletion`. Its graph parameter is the ordinary clique-minor number h(G). The contemplated direction was an absolute linear bound for correspondence coloring in terms of h(G), using the actual eligible-set/palette construction rather than simply renaming lists.

The source's list operation uses a globally named color's single bin to ensure no conflicts between different bins. For a correspondence cover, this compatibility would require the bin assignment to agree along every forbidden matching pair. The actual I22 body, Section 6, already identifies and proves the obstruction: on C4 with k entries per vertex, use identity matchings on three edges and a cyclic shift by one on the last edge. The graph of forbidden pairs is a connected 4k-cycle, forcing every such bin assignment to be constant. This holds for arbitrarily large k even though the assignment is colorable for k>=3. It is a failure of the globally compatible-bin scheme, not a lower bound refuting the desired linear correspondence theorem.

The strongest primary interface checked was Dvořák–Yepremyan, [*Correspondence coloring of random graphs*, arXiv:2307.15048v1, Theorem 2.2, Observation 2.4, and the appendix proof of Theorem 2.2](https://arxiv.org/pdf/2307.15048v1). Its input is a maximum-degree scale Delta and independent-set richness in relevant neighborhood subgraphs, with b(Delta)<=Delta^o(1). The appendix uses a random partial coloring, available-color estimates, a local lemma, and greedy completion. Its conclusion has scale Delta/b(Delta). A clique-minor bound does not by itself provide the needed uniform maximum-degree/neighborhood input with an absolute constant in h. The source's arbitrary eligible sets do not silently control arbitrary forbidden matching pairs across independently partitioned palettes.

This is the same unresolved interface already exposed in I22. No different reservation or conflict-removal invariant was derived. Source 184 was excluded from fresh work by the assignment and was not newly downloaded or reopened; its role in I22 was read as history only.

Companion statement checks: the pinned Hadwiger-counterexample introduction explicitly includes the ordinary fractional-coloring violation; the Colin-de-Verdière companion introduction explicitly derives the linear list-coloring bound in mu+1 from the positive source and minor monotonicity. Those transfers are already paid. Only introductions were read here, with a truncation limitation for the longer Colin-de-Verdière introduction; the counterexample proof bodies were not read or audited. No companion negative statement is treated as a contradiction to a stipulated source.

## 186: product-space influence to a fixed-cardinality layer

The graph source gives a Boolean variance bound with pivotal influences and coefficient 2^17/(log n)^2, uniformly in the product bias. Its actual block restriction retains all edges incident with the block, averages exterior assignments without a degree restriction, and captures a support through one nonisolated vertex of low support degree. The hypergraph companion uses the corresponding minimum-degree capture exponent r/(r-1), and already includes threshold integration. Those operations are stipulated, not reconstructed from an abstract.

The possible compatibility issue was a fixed number m of edges, where coordinates are dependent. Before any freeze, I60 Section 3 was located and read in full for the relevant transfer. It already gives the following route. Let N be the number of coordinates, 0<m<N, p=m/N, and delta_m the disagreement probability under a uniform directed swap from a uniform m-set. Extend a Boolean layer function to every k-set by uniform completion if k<m and deletion if k>m. Every layer mean is the original mean. Conditional slice Poincare gives a variance loss at most |k-m| delta_m/2; adjacent-layer coupling gives total averaged L1 coordinate gradient at most N delta_m. Apply the product source to all Boolean level sets and integrate. For product coefficient a this yields

    Var_layer(f) <= (a N + E|Bin(N,p)-m|/2) delta_m
                 <= (a N + sqrt(Np(1-p))/2) delta_m.

This route is already fully written in I60 and already records the appropriate normalized influence. It does not remove the density factor from a differently normalized Dirichlet quantity. Empty and full layers are singleton spaces. It also does not assert an L2 spectral gap for arbitrary real functions or a noise-sensitivity theorem: the extension uses Boolean coarea and L1 gradients.

The primary normalization was checked directly in Filmus, [*An orthogonal basis for functions over a slice of the Boolean hypercube*, arXiv:1406.0142v2, Lemmas 5.5–5.6](https://arxiv.org/pdf/1406.0142v2). The transposition eigenvalues are j(N+1-j); the resulting Poincare form has coefficient 1/(2N) for the sum over unordered coordinate pairs of squared differences. Both lemma proofs were read, not just their statements. The earlier construction of the basis was not reread.

No unpaid operation remains in this contemplated transfer after the actual I60 body is checked. Neither a parameter variant nor a renamed restricted-space formulation is nominated. The graph restriction and threshold proof, and the hypergraph restriction, completion, and Fourier proof sections were inspected; acquisition and truncation limits are in the ledger.
