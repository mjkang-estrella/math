# 184 — local palettes without a global floor fail before freezing

This is a feasibility screen, not a frozen target or a nomination. The question examined was whether, for each fixed forbidden clique size r>=3, constants C and d0 could guarantee correspondence coloring from lists of size at least ceil(C deg(v)/log deg(v)) on every K_r-free graph of minimum degree at least d0, independently of its maximum degree. All constants must precede the graph. This unrestricted local formulation is false already for ordinary lists on bipartite graphs.

The strongest source operation was checked first. In the pinned correspondence manuscript, `thm:main` and `cor:forbidden` have the global maximum-degree scale. `rounds.tex` does more than quote a uniform coloring theorem: `prop:one-round` accepts nonuniform entry weights, controls the list mass, entropy/edge potential, and remaining degree simultaneously. Nevertheless, equations `eq:round-constants`, `eq:round-parameters`, `eq:weight-bounds` use one k=ceil(C Delta/log Delta), one weight reference K/k, one activation time Delta^(-0.10), and an additive normalized-degree error Delta^(-0.14). The complete completion proof pays this error against a supply of order Delta^0.99. Arbitrary weighted entries are not an unrestricted vertexwise-palette theorem. The same-family independence companion has a different output, an independent set in terms of average degree, not one color for every list.

The decisive primary is Davies–de Joannis de Verclos–Kang–Pirot, *Colouring triangle-free graphs with local list sizes*, [arXiv:1812.01534v2](https://arxiv.org/pdf/1812.01534v2), Section 7, Proposition 11 and its full recursion. Their preceding text expressly allows replacement of d/log d by a sublinear superlogarithmic function. The following integer-choice version checks the needed arbitrary constant rather than inferring it from the coefficient-one displayed statement.

Fix C>0 and a desired minimum degree d0. Choose an integer D>=max(C,1), and an integer delta>=max(d0,3) with log delta>=2D. Start with a star having delta leaves, center list of delta distinct colors, and leaf j forced to the jth center color. This instance is uncolorable. Call its sides A0 (the center), B0 (the leaves), and put b0=delta.

At stage i all B_i vertices have degree and list size i+1; all A_i vertices have degree at least delta and lists meeting the required C d/log d bound. Let

    M_i = 2^(4 D b_i),       b_(i+1) = M_i b_i.

Take M_i disjoint copies of the entire instance, and add a new vertex a on the A side adjacent to every B vertex of every copy. Give a one distinct fresh color c_j for each copy j. Add c_j to every B-list in that copy. Old A degrees/lists do not change; B degree and list size both increase by one. The new vertex has degree M_i b_i and list size M_i. Since

    log(M_i b_i) >= 4 D b_i log 2 > C b_i,

its integer list size is at least ceil(C M_i b_i/log(M_i b_i)). If a is colored c_j, the B vertices of copy j cannot use their new color, leaving an uncolorable copy of the previous instance. Thus uncolorability persists, with bipartiteness.

After delta-1 stages every B vertex has degree/list size delta; the initial A centers also satisfy the bound since log delta>=C. All later A vertices satisfy it by the inequality above. The graph has minimum degree at least delta>=d0. Every list meets the proposed bound and there is no list coloring. Ordinary list assignments are correspondence assignments via equal-color matchings. Consequently no choice of C,d0 repairs the unrestricted local statement. Every graph here is finite; the huge numbers are a legitimate existential construction, not an efficient algorithm or a finite-test argument.

This is the primary's recursive obstruction with explicitly rounded copy counts. It is not offered as a new frontier theorem. It does not dispute the stipulated source or refute local bounds with a Delta-dependent floor. Dhawan, [arXiv:2403.03054v3](https://arxiv.org/pdf/2403.03054v3), Theorems 1.9–1.10, supplies an actual stronger local correspondence comparator with minimum-degree conditions and a log-log loss. Those statements were read; their complete proofs were not. No claim that source184 removes that loss under the same local hypotheses is made.

Historical comparisons: I22 section C and r108 item 4 already examine a different Hadwiger-number DP interface and its palette compatibility. They are not relabelled here. No new target was frozen after the local-degree feasibility failure, and no floor-restricted substitute is nominated.
