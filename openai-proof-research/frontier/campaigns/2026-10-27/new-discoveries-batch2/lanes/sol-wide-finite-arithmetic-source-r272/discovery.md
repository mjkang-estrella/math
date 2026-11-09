# Cabello exact simultaneous-coloring bound: HOLD

Source: Bousquet–Durain, Discrete Math.343 (2020)111781, frozen 2001.01463v1 Question4 p3. Scope is all finite simple loopless G1,G2 on the same V, degrees at most an arbitrary integer Δ, including shared edges that must receive one common color. Target χ′(G1,G2)≤Δ+2. No proof or counterexample obtained.

Chronology: source v1 January2020; 2411.04071v1 November2024 proves asymptotic simultaneous coloring; 2605.05046v2 is later sampling work, whose introduction still distinguishes the exact conjecture from the asymptotic result. Exact API timestamps are retained in chronology.json, distinct from dates printed in the PDF. The sampling theorem does not reach Δ+2. Current registry head and exhaustive specialist prior status are unavailable. No acceptance requested.

Strongest classical objection: 2411.04071v1 already reduces the problem to local sunflower/profile hypergraphs, proves the optimal first-order constant ν(2)=1 and transfers it through its Theorem1.4. Its Lemmas2.6–2.7 and Theorem1.1 proof, and the list-coloring reduction in §3, are the actual nearest route. A profile rederivation, fractional leading constant, or o(Δ) error improvement is not a new resolution. Its Δ≤2 list proof is also already complete. Source2020's balanced-factor proof is another established mechanism and loses approximately Δ/2 colors, not a hidden constant that rounding removes.

## Route A: compatible recoloring

Define C(G1,G2) with one vertex per edge in the union. Two vertices are adjacent exactly when the corresponding edges share an endpoint and coexist in at least one Gi. Proper vertex colorings of C are exactly simultaneous edge colorings: this follows separately for each coexisting incident pair, in both directions. Thus two-color swaps on connected components of C preserve validity.

Attempt: insert one uncolored edge using alternating components, then induct over edge count. The following precise universal lemma would suffice, but is UNPROVED: for every such pair, every edge e, and every proper coloring of C−e with palette [Δ+2], a finite sequence of swaps on connected components induced by two colors, together with single-vertex proper recolorings, reaches a coloring in which some palette color is absent from N_C(e). A proof would yield the source bound by induction; a partial coloring whose entire move component has no extendible state would decisively refute this stronger route. We do not assume reconfiguration connectivity.

Why ordinary Vizing fans do not directly transfer: a common edge must respect constraints in both graphs; swapping along a chain computed in only one layer may break the other layer. C is not generally a line graph. Exact induced-claw witness: G1={01,02,13}, G2={01,04}; its conflict graph has center01 and independent leaves02,13,04. Every line graph is claw-free (three mutually nonincident edges cannot each meet both endpoints of one edge). Therefore a blanket “apply Vizing to C as a line graph” shortcut is rigorously false. The witness is not a counterexample to Cabello.

Even precoloring the shared graph and extending each layer is not uniformly valid. Let H have edges02,03,04,15,16,17, colored 0,1,2,3,4,5 respectively. Let G1=H+01 and G2=H. Here Δ=4 and H is properly colored, but 01 sees all six colors, so this fixed shared precoloring does not extend using Δ+2 colors. Recoloring H solves this instance; it refutes the arbitrary-extension lemma, not the conjecture. The favorable Δ≤2 extension argument in the 2024 paper cannot be imported universally.

Decisive next calculation: search for a small Δ≥3 partial simultaneous coloring whose two-color/single-vertex move component has no insertion state; retain exact component certificates and color-symmetry quotient correctness. The completed four-vertex census checks existence only, not this stronger reconfiguration lemma. It is diagnostic and does not justify that next lemma.

## Route B: compatible matching decomposition

For each original vertex v create two vertices (v,1),(v,2). Replace an edge uv exclusive to Gi by the 2-set {(u,i),(v,i)}, and a shared edge by the 4-set {(u,1),(v,1),(u,2),(v,2)}. Call the resulting hypergraph H. Two hyperedges intersect iff their original edges conflict in C. Consequently a matching in H is exactly a simultaneous color class; partitioning E(H) into Δ+2 matchings is the exact desired endpoint. Each split vertex has degree≤Δ. This equivalence includes every shared-edge constraint; ordinary separate edge colorings omit it.

A hoped-for plan was to prove a fractional compatible-matching cover bound and round with bounded additive loss. To be precise, let M range over matchings in H, and χ_f=min Σ_M x_M subject to x_M≥0 and Σ_(M∋e)x_M≥1 for each e. Its elementary finite LP dual maximizes Σ_e y_e subject to y_e≥0 and Σ_(e∈M)y_e≤1 for every compatible matching. A sufficient pair of universal missing inequalities would be χ_f≤Δ+1 and χ(C)≤ceil(χ_f)+1 for these H. Neither is proved here. This is a clearly specified stronger route, not a citation to a generic rank-four coloring theorem.

Why generic low-codegree/nibble rounding does not give an additive constant: the pair (v,1),(v,2) occurs in every shared edge incident to v, so its codegree can equal Δ. This persists on stars for arbitrarily large Δ, despite original simplicity. Moreover an o(Δ) remainder can grow, for example floor(sqrt(Δ)); integer-valuedness never changes it to≤2. The actual 2024 sunflower handling is essential to the known asymptotic result and supplies no asserted constant-error rounding.

Decisive next calculation: for explicit Δ≥3 pairs solve the compatible-matching LP exactly and seek a dual witness above Δ+1 or an integral/fractional gap exceeding one. Such a witness kills the respective sufficient inequality without refuting the original source bound. No fractional certificate has been computed or claimed. The split hypergraph and LP are a reduction only, uncredited.

## Exact bounded evidence and conclusion

checks.py verifies both shortcut falsifiers and enumerates all 64²=4096 ordered pairs of simple graphs on four labeled vertices using exact backtracking at palette Δ+2. All are colorable; largest search visits seven nodes. Most are already covered by elementary bounds or public small-degree cases. No novelty, minimality or universal conclusion follows. Fixed 200000-node per-instance cap and helper_guard apply; no numerical libraries, Lean or manuscript.

The best candidate remains HOLD with substantial universal gaps. The two mechanisms were developed beyond their first failed shortcuts, but neither gives a reason to claim the exact bound tractable. Root should prefer a newly sourced candidate over an indefinite blind census. No PROOF.md is appropriate.
