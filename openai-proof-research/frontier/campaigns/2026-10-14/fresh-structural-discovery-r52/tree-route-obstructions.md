# Source118 quantitative-tree routes: bounded findings

Status: no source118 target was frozen and no candidate is nominated. This is a continuation of the source118 operation check, not a lower bound on all possible competing trees or bin-packing gaps. Source theorem truth at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb is stipulated.

## Contiguous spider phases have an exponential cost

Consider the particular phase template with M roots. Root i has k ell_i disjoint spider legs, with k special endpoints at each integer depth in the block {b_i+1,...,b_i+ell_i}, where b_i=sum_{j<i} ell_j. Legs are disjoint after the root. A defender chooses at most one non-root vertex at each depth. Each chosen leg protects one special endpoint, and its protection can be scheduled at any time up to that endpoint's depth. The maximum protected endpoint count at root i is min(k ell_i,b_i+ell_i). Indeed the unit jobs with those deadlines have this maximum feasible cardinality: for each terminal segment of jobs the deadline-count bound is weakest at an endpoint of the block; equivalently greedy earliest-deadline scheduling rejects exactly max(0,(k-1)ell_i-b_i) jobs. A protected job is realized by the vertex of its private leg at its scheduled time.

Suppose the phase requires, for EVERY singleton incoming root, survival of at least fraction 1-1/k-delta of its equally weighted special endpoints, where 0<delta<1-1/k. Then the minimum in the preceding formula cannot be k ell_i. Consequently

b_i+ell_i <= (1/k+delta)k ell_i,

and ell_i >= b_i/(k delta). For b_i>0, b_{i+1} >= (1+1/(k delta))b_i. Thus this exact contiguous-block spider template has exponential depth cost in the number of incoming roots. Altering block lengths alone cannot give a polynomial-cost phase with the stated singleton survival guarantee. The claim concerns this template and its uniform endpoint masses; it does not rule out overlapping resources, nonuniform masses, another tree structure, or a different global induction.

This matches the operative Chalermsook–Vaz good-gadget construction, whose phase size is (k/delta)^{O(M)}. Iteration gives towers, as the paper explicitly records. No new efficient replacement has been constructed here.

## Unequal labels can recycle globally using one extra bin

Use an actual YES instance of source118 with n vertex labels and its completeness packing into B bins; take all vertices in the selected cover, so one plus-side funded root template bin is present for each label. Choose one such X/ZA/U/DM/FT five-item bin for each label v=1,...,n, all with the same template role. Denote its ZA anchor by A_v. Shift anchors cyclically: bin v receives A_{v+1} for v<n, and bin n receives A_1. Retain every other physical item.

For v<n the primary coordinate still sums to zero, while the secondary score is 2*3^v-2*3^{v+1}<0. Source sizes have the form 1/5+gamma p+mu q+nu w; the five-item coordinate remainder has absolute value at most 30 nu and 30 nu/mu=3/100. Thus the negative integral secondary score dominates the final coordinate, and each of these n-1 unequal-label bins is feasible. Split the remaining five-item tuple into four items and one item. Every source item is less than 7/30, so both new bins are feasible. This gives a packing in B+1 bins with n-1 unequal-label full table bins, preserving every physical item exactly once.

This refutes a proposed GLOBAL O(c) bound on the number of unequal-label table bins in B+c packings of these source instances. It is consistent with the source's per-vertex O(c) accounting. It does not disprove a larger additive gap, a direct-sum theorem with another isolation mechanism, or the existence of a better competing-tree construction.

## Primary reading boundary

Chalermsook–Chuzhoy, Resource Minimization for Fire Containment (SODA2010), author PDF https://home.ttic.edu/~cjulia/papers/firefighters.pdf: read raw extracted lines309–610 (preliminaries, amortized formulation, full main iteration) and1506–1905 (section6 gadget/analysis through its end). The technical rounding proof in sections4–5 was not read. Its rounding guarantee contains an additive prefix-time term. The uniform integer optimum is at least one. Therefore the O(log* n) approximation must NOT be quoted as a purely multiplicative integrality-gap upper bound for a nonuniform competing-tree LP with fractional value2/d<1.

Chalermsook–Vaz, New Integrality Gap Results for the Firefighters Problem on Trees, arXiv:1601.02388: read extracted lines272–430, the good-gadget definition, iteration, and complete section3.1 construction/proof. Later strengthened-LP results were not read. Lemma4 has (k/delta)^{O(M)} size; repeated phases have tower growth. Primary receipt hashes are in primary-receipts.json. The raw CC extraction was produced separately and will be recorded before sealing.

Source118: r51 already records complete operative reads of trees.tex, instance.tex, completeness.tex, consequences.tex and introduction.tex. During r52 the bibliography lines1–80 were additionally read; trees.tex was subsequently reread completely, and instance.tex305–375 plus completeness.tex1–100 were reread for the packing modification. No claim that soundness.tex beyond lines1–80 was read. Those bodies remain private and immutable in r51. No upstream truth audit was performed.

## Disposition

No credible new quantitative tree/resource mechanism emerged from these two routes. Parent authorized continuation of the unchanged r33 Eulerian directed-cycle target. These obstructions are retained as scoped method failures; they are not a nomination and do not increment the campaign count.
