# MathDB 352827: unit-gap counterexample diagnostic

Status: HOLD, zero accepted credit, no Lean endpoint and no journal-scope clearance.

Both arXiv:2112.01884v1 and v2 were retrieved and text-extracted. The source defines SG(n,k) as the graph of cyclically 2-stable k-subsets of [n], with disjointness adjacency. Conjecture 2 in v2 asks that the diameter drop from n=2k+r to n+1 is at most 1 for 2≤r≤k−2.

The exhaustive search gives D(SG(22,10))=8 and D(SG(23,10))=6. Thus k=10,r=2 gives drop 2. The respective graphs have 121 and 506 vertices, and 330 and 3841 edges. Source computation Table 1 only reaches k=7, so this is beyond that reported range.

Two implementations agree. `schrijver.py` generates stable sets by compressing the gaps between selected positions and does BFS from one representative of each dihedral orbit. `verify_schrijver.py` independently enumerates all k-subsets directly and filters the cyclic adjacency condition, then performs BFS from EVERY vertex without symmetry reduction. For every row it checks both the predecessor paths and the 1-Lipschitz condition on every edge. Full vertices, adjacency, distance matrices and predecessor matrices are in `outputs/SG-22-10-certificate.json` and `outputs/SG-23-10-certificate.json`. A certified distance labelling with source label 0 proves lower distances; predecessor paths prove upper distances. Source and target pair labels are in `outputs/schrijver-independent.json`.

Important source-fidelity objection: these computations also give D(SG(14,6))=5, whereas the arXiv Theorem 6 and Table 1 print 4. Thus the source's r=2 theorem/data are inconsistent with the computed graph metric. This is not being counted as a correction of Theorem 6. The precise journal Conjecture 2 may have changed. The 2024 journal version, Discrete Applied Mathematics 350,15–30, DOI 10.1016/j.dam.2024.02.019, was identified but its full body remains unread. Inherited ScienceDirect denial was not retried. Consequently root must resolve this source gap before deciding whether there is a substantive surviving conjecture. Search outputs `web-schrijf-prior*.json` record bounded prior searches; none establishes worldwide novelty.

No analogous monotonicity counterexample (352826) occurred in the tested consecutive pairs. The first search's exact finite coverage is its complete output file; it uses k=2..10, r=1..min(6,k−1), retaining only instances with ≤6000 vertices. It does NOT prove either universal statement or minimality across all parameters.

Formalization route if journal scope survives: use recursive stable-word generation and prove its completeness, then a sound graph-distance certificate checker. Transfer its distances to the literal finite-set Schrijver graph. The 506×506 distance matrix alone is not a Lean theorem, nor is a theorem about an unbridged 506-element surrogate graph. No dummy endpoint has been supplied.
