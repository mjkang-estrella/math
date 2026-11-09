# Expanded corpus r100: bounded discovery packet

No qualifying new solution or full literal Lean endpoint was obtained. Accepted credit is zero for every entry. Counts and shared campaign files are unchanged.

This packet contains exactly 20 ID-keyed dispositions in `results.json`, the 20 verbatim raw corpus lines (including their newlines), one-based locations and SHA-256 provenance in `extracted.json`, all 20 primary-source HTML bodies and dated HTTP/hash receipts, follow-up primary papers, reproducible diagnostic scripts, full process logs and capped-run receipts.

## Decisive exclusions

- **364725:** already proved in Kaul–Mudrock–Straub, arXiv:2607.16810. The current source explicitly reports this. The successor proves the stronger equality for every n,k. Its shifting proof (statement 1.5 / proof 2.4) was read; this is not a catalogue-only exclusion.
- **348914:** the six-cycle search found a symbolic obstruction beyond the source's checked 3-,4-,5-cycles. Subsequent primary-paper checking found Göbel–Misra, arXiv:2506.23936, Section 4 / Example 4.4, which already refutes the conjecture even with one vertex color. No discovery credit or Lean investment.
- **346405:** exact reliability counts refute the FCG claim, but **the source's own Figure 7(c) already does so**. The retrieved SVG gives a Hamiltonian 10-cycle with chords (0,6),(1,4),(2,7),(3,9),(5,8). Its exact spanning-tree count is 1,920 versus 1,815 for FCG(10,5). The conjecture's divisibility condition holds (10=2·5). This is a zero-credit source-internal contradiction, not a new research result. The complete connected-edge-subset counts were independently enumerated for search witnesses at orders 10 and 12; componentwise dominance was verified.

## Completed bounded searches

- **346135, shortened Reed–Muller generator weights:** exact existential successes at every degree m=5 through 20, beyond the source's table m=5 through 9. Complement-root products and exact binary polynomial division avoid multiplying exponentially many roots. The degree-20 successful primitive modulus is 1,048,659, with generator weight 524,800 > 262,144. No all-degree construction or refutation.
- **346233, PcN exponents:** p=11, extension degree 7, beyond source primes 3,5,7. All 995 nonlisted odd exponents d≤2001 fail either the a=0 power-permutation condition or an exact a=1 collision. Initial 8,192 distinct sampled inputs left 153 survivors; refinement with 65,536 distinct inputs rejected all of them. Every retained collision was independently recomputed using scalar finite-field arithmetic, and irreducibility of X^7+X+4 was checked. This is not the full p=11 classification.
- **345665, skew shapes:** all monotone-endpoint n×n shapes admitting a transversal, n=2 through 6, and all diagonal sizes 2 through n. 19,413 shapes; no violation. Occurrences require the entire selected square subshape, as in the source, rather than ordinary permutation subsequences. Source gives no numeric exhaustive range, so surpassing its search cannot be claimed.
- **345194, grid complexes:** 55 exact mod-2 Alexander-dual homology calculations: n=2 through 6, n≤r<2n, and n=10 through 16, 2n−5≤r<2n. No off-target reduced homology. Source table stops at n≤9,r≤9. Neither integral torsion nor homotopy types are certified. The difficult central case n=r=10 remains uncomputed.
- **352596, matroid flag numerators:** 190 binary represented matroid instances, ranks 3 through 5, with at most 10 columns. Exact flat lattices, interval Möbius functions and flag sums satisfy both coefficient bounds. The source's strict-order convention was respected. No exhaustive all-matroid claim.
- **352123, Bruhat reconstruction:** 400 sampled intervals in S8 (type A7), requested rank differences 4 through 6, at most 104 vertices. Recursive lower-cover deck fingerprints produced no mismatch lead. This goes beyond the source's ambient A6, but fingerprints are not certified poset-isomorphism classes and do not verify the conjecture on the samples.
- **347553, weak order T3 inequalities:** exact weak-order multiplicity dynamic optimization through n=100 supports validity of the intended two representative inequalities; reversal/relabeling covers the other rows. This goes beyond n=10, **but does not check facets**. The printed double-sum placement is ambiguous: the implementation counts each fixed–unfixed arc once. No literal endpoint is claimed.
- **347241, block graphs:** 7,200 seeded attached-clique graphs at q∈{2,3,4,6}, b∈{3,4,6,10,15,25}; five polynomial evaluations above the graph's spectral radius. No numerical violation. This is a floating-point sample, not an exact ray-positivity certificate. A later primary-paper abstract reports the weaker spectral-radius conjecture proved by Zhao–Liu (2023); that proof body and the stronger-order scope remain unread.
- **347800, disk metrics:** 100,000 seeded hyperbolic configurations, with clause 2 evaluated only for the 69,296 configurations whose Euclidean rotated endpoint lies inside the disk. No numerical violation. Exact source piecewise formulas were used. No proof or exact counterexample.

The cycle and reliability searches above also have retained scripts, complete outputs, and precise stopping rules.

## Source-lemma gate and remaining work

Every entry explicitly records which source ingredients were checked and why no full-scope source-only combination was established. Review depth is not uniform: several hard infinite targets received only a source-backed disposition, not a full theorem/proof-body audit. The known special cases, the source's own data, and the adjacent r88 quadratic spectral-containment investigation are not credited again.

**The assignment's requested several-hour, all-finite-target deep pass is not fully completed.** In particular, there is no new certified redundancy LP for 352570, no certified equivariant-cover computation for 352215, no exact Bruhat isomorphism engine, no T3 facet-rank sweep, no complete p=11 PcN classification, and no central-width-10 grid calculation. These gaps are explicit in `results.json`. The asymptotic shuffle-square, forwarding, path-averaging, repetition-threshold and infinite-operator targets remain parked with their actual source statements and identified gaps. This packet must not be interpreted as exhaustive technical review or a completed discovery campaign.

## Access, provenance and validation

Live registry requests were only to `/commits/HEAD`: OpenAI/math returned `4eaee87548250b2682affda7d05d947c05554bae`; Omega returned `2a73b52adab1ec236edc18a09df195ce0ce54e58`. Cached complete D5/Problems listings were screened separately, with hashes and limitations. Omega's changed HEAD is not cleared by a cached path listing. No live `/commits/main`, denied-route retry, browser tab, external message or upload was used. General web search located primary follow-ups; hashed retrieved primary bodies, rather than search snippets, support the two known-resolution exclusions. The block-graph lead remains explicitly body-unread.

No Lean packet is supplied because no genuine qualifying endpoint survived. No axiom/replay claim is made. Numerical and exact Python computations remain diagnostics until formal semantics are certified.

Runs used the copied `scripts/limited.py` wrapper: at most two CPUs, 120 CPU seconds / 140 wall seconds, sampled process RSS stop at 6 GiB, 12 GiB address-space cap. This is sampled process monitoring, not a cgroup or transient/descendant-memory guarantee. The attempted C++ build could not run because g++ is absent; its log is retained, and the executed finite-field search is the Python version. All launched processes are complete at handback. No child agents, git operations, shared-index edits, or writes outside this lane were intentionally performed.

Reproduce individual runs from this directory with, for example, `python scripts/limited.py rm-replay python scripts/rm.py 17 20`. PcN refinement requires the initial `outputs/pcn.json`. Running `scripts/report.py` regenerates results from the retained notes and metadata. `outputs/manifest.json` records the final evidence hashes.
