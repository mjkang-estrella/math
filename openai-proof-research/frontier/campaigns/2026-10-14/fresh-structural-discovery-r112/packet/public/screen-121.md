# 121: metric-weighted edit distance — pre-freeze compatibility remains unresolved

This is a feasibility screen, not a frozen target, full theorem, or nominee. The question investigated was whether source121's near-linear, fixed-accuracy approximation mechanism extends to arbitrary metric insertion/deletion/substitution costs. No bounded aspect ratio, fixed alphabet, or additive-error replacement was selected. An exact binary input model and its constant dependencies were not frozen because the operative compatibility step was not obtained.

## Paid source contract

At the pinned revision, `An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/build/sections/01-introduction.tex`, `thm:main`, estimates unit-cost distance with probability at least 2/3. For each fixed rational accuracy, its worst-case expected work is N^{1+o(1)} on a logarithmic-word RAM, including all preprocessing and arithmetic. Symbols have polynomially bounded integer labels; equality returns zero deterministically. This is not already a theorem for arbitrary rational metric tables.

The actual operations in `02-geometry.tex`, `lem:geometry`, and `03-seed.tex`, `thm:seed` and `lem:shift-tree`, matter. Endpoint movement and connecting child paths cost their index displacement; the leaf formula uses occurrences of a single symbol. The shift-tree recurrence charges twice the shift displacement. The lazy random table simultaneously upper approximates all states with a polylogarithmic seed factor, with conditional expected first-query work of (1+|I|)2^{o(H)} even for adaptive queries. Threshold pruning, zero states, and deferred independent entry seeds are part of that contract. Merely giving fast weighted pairwise distance estimates would not discharge this contract.

## Strongest primary repair actually tried

Mader–Tavasoli–Wang, [2609.14873v1](https://arxiv.org/pdf/2609.14873v1), was read beyond its abstract: clipped prefix masses and Lemma 3.1; sparse assembly in Lemmas 4.1–4.2; rough approximation Theorem 5.1 and Lemma 5.2; the full proofs in §6, including Lemmas 6.2–6.4 and Corollary 6.5; and Lemma 7.1 and the inward-snapping discussion in §7.1.

Let g(a) be the cost of deleting character a and g_t(a)=min(g(a),t). The triangle inequality implies that the discrepancy between clipped prefix masses is bounded by the cost of an alignment prefix. This supplies a better coordinate than raw length. But clipping alone does not bound the actual cost of deleting a heavy character. The primary construction addresses precisely this: its grids keep both adjacent cuts around heavy characters and group light characters in increments proportional to εt. Inward rounding then deletes only light mass and pays O(εt) in true cost.

The long-window reduction also does more than discard cheap characters. At threshold H=εt/d it explicitly pays the full removed deletion costs. Matching savings involving removed characters lose at most 2H per match, hence at most 2εt over at most d matches. The retained comparison window has O(d+d/ε) characters, allowing bounded exact computation. Finally, the sparse box dynamic program assembles a compatible chain in O(n+P log n) work. These operations were checked before diagnosing a gap; raw-index failure alone is not the reason for this screen's outcome.

The remaining issue is simultaneous refinement at near-unit multiplicative accuracy. The shared-center comparison in Corollary 6.5 pays D_V+(2+2ε)t: the center path is used twice. This is an order-t loss, not a precision error that vanishes by shrinking ε. Clipped coordinates also change with the cost scale. No construction here supplies a single lazily evaluable simultaneous table, with the source's adaptive-query work guarantee, whose repeated refinements and original-cost connectors remove this loss. The source's unit-cost length bounds and leaf recurrence do not themselves give that construction.

## Boundary

This does not refute an all-metric near-linear scheme, nor establish that the read primary cannot be improved. It records an unproved compatibility operation. There is no frozen scope, no restricted substitute, and no new mathematical acceptance claim. The older r58 cyclic-distance report was read as history; it concerns a different already investigated route and was not resumed. Later source refinement sections and the primary's remaining sections were not fully read, so this screen is not a worldwide priority clearance or an exhaustive impossibility assertion.
