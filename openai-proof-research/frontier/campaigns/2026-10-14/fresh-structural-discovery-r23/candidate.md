# R23: bounded-VC deduction and a failed equality replacement

Status: pre-freeze screen, no substantial nominee. Family 190. No full research target was frozen. The complete deductions below are technical; the bounded-ladder interface at the end remains unpaid. No campaign count increment or self-PASS is requested.

## Source contract and conventions

Use the pinned manuscript *Polynomial removal fails for ordered binary matrices*, revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, with all six sections and the construction companion figure. Its truth is stipulated. The receipt records the nine actual source blobs. Let H be its fixed 66×66 binary pattern, with 64×64 anchor S and body P=((1,0),(1,1)). An ordered copy chooses strictly increasing row and column sets separately and matches every entry, including zeros. Edits can change either bit. Write N_H(M) for the number of copies and Δ_H(M) for minimum edit count divided by n².

For every h≥1, put m=2^h, d=386h+2 and n=dm. The source's A_h has N_H(A_h)/n^132≤d^-2·2^-h and Δ_H(A_h)≥d^-2 (Theorem `thm:main`, Propositions `prop:distance`, `prop:copy-count`). The prescribed source blocks, orders and modes below are those of equations `eq:tree-orders`, `eq:body-modes`, `eq:variable-entries`. An internal level has two signs, each with m total positions per axis, split into node blocks of size m/2^i. The leaf signs coincide, with singleton blocks. There are 6h modes; each has 64 anchor groups per axis, all of size m. Dummy groups each have size m.

The source's testing corollary concerns uniform independent row/column sampling and rejection upon finding H. It does not establish the same quantitative lower bound for arbitrary adaptive testers.

## Complete technical deduction: uniformly bounded VC dimension

For every h, both the row-neighborhood and column-neighborhood set systems of A_h have VC dimension at most 11. Here VC dimension uses arbitrary selected positions, independent of their order.

Fix q≥1 selected columns Y. We bound the number of different row traces by 16q²+84q+4.

First consider anchor rows. At most q modes contain selected anchor columns. The anchor rows of these modes have at most 64q different traces, because each mode has only 64 row types. Every other mode gives zero on all selected anchor columns. Its possible nonzero traces on the other columns are intersections with its two designated body-column sets. These sets are the dummy class, a whole signed level, or a fixed-parity part of a signed level. The leaf class is counted with its sign identification. A selected variable column belongs to at most four mode-role sets, by `lem:mode-incidences`. Consequently at most 4q distinct nonempty traces arise from the variable-column role sets; the dummy role set and the empty trace add at most two. Thus all anchor rows contribute at most 68q+2 traces.

Next consider variable rows. A selected anchor column has nonzero entries only at the at most two variable-row depths specified by its mode. A selected variable column at depth j can interact only with rows at depths j and j+1. Thus at most 4q depths are active. At every other depth the variable-row trace is the same fixed set of selected dummy columns. At a fixed active depth, split variable rows into at most four classes by sign and node-index parity (the common leaf needs only two). In such a class all incidences with selected anchors and dummies are constant. Every entry against a selected variable column is a monotone threshold in the row node p or its parent floor(p/2). All these thresholds change in the same direction. There are at most q+1 different traces in that class. Variable rows therefore contribute at most 16q(q+1)+1 traces. Dummy rows contribute one. The total is the stated bound.

The same argument with axes interchanged applies: selected anchor rows activate at most two column depths each; a selected variable row activates only its own and the preceding column depth. At a fixed sign/parity/depth, its entries as the column node varies are monotone thresholds. The same bound follows. At q=12 it equals 3316<4096, so no 12-position set is shattered on either axis. Any larger shattered set would contain a shattered 12-position subset.

This immediately specializes the source obstruction to a class with bounded VC dimension on both axes. It is not a new construction or a substantial operation. The distinction from stability is essential: the m×m shared leaf block is exactly (1[p≤q]) and supplies arbitrarily long half-graphs as h grows.

## Complete obstruction to the attempted equality replacement

Define a fully specified alternate matrix B_h for every h≥2. Keep H, all physical positions, orders, anchors, dummy rules and mode incidences exactly as in the source. Change only the variable-entry table as follows:

- The plus same-level rule, including the common leaf, becomes 1[p=q].
- The plus child-row/parent-column rule becomes 1[floor(p/2)=q].
- Both internal-minus strict-threshold rules become identically zero.
- Every remaining variable entry remains zero.

The common leaf is assigned by the first rule. The minus child-row rule at the leaf is zero. This is a binary n×n matrix with exactly the source dimensions.

### The edit lower bound survives

For every h≥2, Δ_H(B_h)≥d^-2. Indeed the source's protected-selection argument depends only on anchors, dummy incidences and the two root bits; these have not changed. More explicitly, choose a uniform leaf, the associated ancestor node at each level on each axis, independent uniform positions inside its blocks, and independent uniform anchor/dummy representatives. Each selected whole-level position is uniform in its m-position class. Every fixed protected cell (at least one endpoint an anchor or dummy, or both endpoints roots) is selected with probability at most m^-2. Fewer than m² arbitrary edits therefore admit a selection avoiding all edited protected cells.

In an H-free edited matrix, no designated body can be P, since its intact anchor representatives would complete it to H. Let x_i^+ and x_i^- denote the selected same-level entries. The root values are x_0^+=1 and x_0^-=0. The vertical plus body has form ((1,u),(1,x_{i-1}^+)); if x_{i-1}^+=1, avoiding P forces u=1. Its horizontal plus body ((u,x_i^+),(1,1)) then forces x_i^+=1. The vertical minus body ((1,x_{i-1}^-),(1,v)) forces v=0 when x_{i-1}^-=0. Its horizontal minus body ((x_i^-,v),(1,1)) then forces x_i^-=0. These four bodies are ordered by the same ancestral-path relations as in the source. At the common leaf x_h^+=x_h^-, a contradiction. No nonprotected initial variable value was used.

### Original copies are already polynomially abundant

For every h≥2,

N_H(B_h) ≥ m^132/8.

Use mode V_2^+. Select a child row at depth 2 with node p=0 or p=1, the plus parent row at node a=1, a dummy column, and the plus parent column at node b=1. The child row precedes the parent row because floor(p/2)=0≤1. The dummy column precedes all variable columns. Their body is P: the two dummy incidences are 1; the child-to-parent entry is 1[0=1]=0; the same-parent entry is 1[1=1]=1. These are exactly the role sets of V_2^+. Any choice of one representative from each of its 64 anchor groups on either axis completes an ordered H copy.

The two child-node blocks together have m/2 positions, the parent row and column blocks each m/2, and the dummy column has m. Thus there are m^4/8 distinct body choices and m^128 independent anchor choices. This proves the bound, including h=2 when the child is already a leaf.

To compare with actual edit distance rather than only the source's lower parameter, zero every one. The zero matrix is H-free. We can overcount the number of ones in B_h by the following disjoint types (overcounting within a type is harmless):

| Type | Upper bound divided by m² |
| --- | ---: |
| Anchor against anchor | 6h·64² = 24576h |
| Anchor against nonanchor, both orientations | 24h |
| Dummy against nonanchor, both orientations | 4h+3 |
| Variable against variable | 4h+1 |

For the second line each of the 6h modes has two unit-vector roles per orientation, each with at most m members. For the third there are (2h+2)m nonanchor positions per axis and the dummy-dummy block is counted once. The fourth allows all h+1 plus same-level products, h minus products, and h products of each parent type, irrespective of how many ones actually remain. Therefore the total is at most (24608h+4)m²≤64dm², and Δ_H(B_h)≤64/d. Combining gives

N_H(B_h)/n^132 ≥ 1/(8d^132) ≥ Δ_H(B_h)^132/(8·64^132).

This particular replacement sequence satisfies a fixed polynomial lower bound in its actual distance. It cannot establish a superpolynomial removal obstruction. No claim is made that B_h has bounded ladder dimension, nor that every equality-based or stable construction is impossible.

## Operation comparison and unpaid interface

Alon–Ben-Eliezer, *Efficient Removal Lemmas for Matrices*, Theorem 1.2, already turns many entry-disjoint original copies into polynomial copy density. Its §4 proof clusters near-identical rows, shifts rows across separators while preserving many original copies, and refines to nearly homogeneous ordered blocks. Theorem 1.5 treats row-permutation-closed forbidden families: representative-row replacement and neighboring-column copying give a repair that creates no forbidden copy. That symmetry is absent for this single ordered H. Neither original-copy hitting sets nor row closeness alone justify arbitrary-edit repair. [Primary PDF](https://web.math.princeton.edu/~nalon/PDFS/testmatrixf4.pdf).

Wang, *A Four-by-Four Obstruction to Polynomial Removal for Ordered Binary Matrices*, arXiv:2610.15370v1, gives a 4×4 obstruction with n=(14h+2)m, exact edit distance m² and exact count 2m^6+(m−2)m^5/2. Its XOR construction assigns m² protected selections with no protected-cell collision. Its canonical dummy-to-leaf repair attains the lower bound. Appendix H compresses any k×k pattern witness with distinct row and column signatures to at most 6k levels by retaining defining, predecessor and first-divergence depths. These already pay natural smaller-pattern, exact-count, derandomization and finite-witness directions. Appendix G states integer certificates for classification and repair; I read that interface but did not execute or independently audit the Lean certificate. [Primary preprint](https://arxiv.org/abs/2610.15370v1).

A possible stronger question would require the host matrices also to avoid half-graphs of one fixed length, while retaining sparse original copies and a large unrestricted edit distance. No target of this kind has been frozen. The source's suppression of off-path copies uses threshold comparisons; the explicit replacement above loses suppression already at depth two. Assigning node-specific anchors is only an undeveloped idea and is not asserted to give either a construction or an impossibility theorem. Stable graph regularity results concern a different ordering interface; no theorem about their sufficiency here is claimed. The bounded search did not resolve the full stable-host question.

The completed mathematical progress is the explicit trace calculation and the quantitative rejection of one concrete replacement. Neither clears the campaign's substantiality gate. No manuscript, formalization or publication is warranted from this screen.
