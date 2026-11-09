# I340 reading, validation, and failed closures

2026-10-13. Research output: unresolved, with proved technical partials. This file records read scope, not an audit of the stipulated upstream theorem.

## Source authentication and scope

Read root `AGENTS.md` and `sources/upstream.json`; the pin matches the assigned fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. `sources/CONTENTS.md` was initially displayed in an overlarge, truncated command, so that display is not claimed as a complete semantic reading. The complete `sources/preprints-tree.json` was independently traversed for manuscript directory names: 749 directories, with the H/P/nonuniqueness kinetic companions and quantum hard-sphere titles distinguished. This was a title/path screen, not reading 749 papers or proving absence of duplicates.

The actual H sections 01–08 and bibliography were fetched from exact pinned raw URLs into tool memory. Their sizes, SHA256 and Git-compatible blob identities are recorded in `input-authentication.json`; the blob identities were checked against the complete preprints inventory without invoking git. Source bodies were not written to disk or copied into a new source cache. After the initial large outputs, section texts were read in bounded slices, including the full statements and proofs in these eight H sections. The first wide filename-discovery command at the parent working directory returned some out-of-project filenames; no out-of-project file contents were read and no writes occurred there. All subsequent shell work used the research root.

The following H passages carry the deductions:

- §01 `ass:kinetic`, `eq:grand-canonical`, `thm:main`, introduction and proof structure: exact whole-space ensemble, arbitrary supplied regular interval, FDD-only scope.
- §02 `prop:initial` and proof: factorial insertion domination, fixed moments of N/μ, exact initial centering; `lem:target-moments`, `lem:target-propagator`, `prop:gaussian-target` and proofs: global spatial integrability, Gaussian exponent allowances, source covariance and weak drift.
- §03 `thm:dhm-package`, its envelope adaptation proof, `lem:dhm-dummies`: fixed kinetic dependencies, partial slab endpoints, coarse exponents, and fixed record/root losses. Restarting forgets collision prehistory, not particle phase points.
- §04 `lem:one-slab-expansion`, `eq:crude-operator`, `prop:one-root`, `lem:marked-regrouping`, `lem:diagram-labels`, `lem:stopped-variation`, `thm:marked-expansion`, `cor:terminal-witness`, and their proofs: actual finite kernels, fresh-label factorials, pulse/segment placement, partial-final-slab variation error, and high-complexity removal before sharp normalization.
- §05 `prop:cutoff` and complete proof chain: primitive-pair gains with both time and velocity restrictions, conditional kernel versus projected-domain distinction, neutral completion, exceptional-piece extraction, common energy containing sets, causal time integration, and final graph summation. The theorem permits η=1/20. It is a global discrepancy estimate, not tightness.
- §06 lines 16–71 and the complete `thm:sharp-cumulants` proof: dependencies on fixed records; merger Jacobian; no free redundant-contact time; the C_K(1+n)^{d_K}(CT/√L)^n majorant; initial-link gains; finite-size dominated convergence for cycles; completeness, traces and last-contact splitting. Weighted retained measures do not give a Gaussian weight for arbitrary microscopic remainders.
- §07 `prop:tree-evolution`, covariance calculation, backward pulse propagation and `prop:cumulant-clt`, with their proofs: the signed limiting tree identities, full joint covariance, fixed-list centered moment convergence, and exact factorial-to-ordinary cumulant formula.
- §08 complete: one set of Γ,L thresholds, exact-centering Hölder comparison, and Cramér–Wold completion of the FDD theorem.

Parent support explicitly supplied for this task was read in full: `frontier/iterations/i340-parent-path-transfer.md` and `frontier/sources/i340_parent_kinetic_paths/reading.md`. Its Gaussian continuity and uniform transfer deductions were independently reconstructed, including exponent p=22 for η=1/20. They do not pay microscopic tightness.

Finalized I20/I23 portions were read only for the kinetic contracts, unresolved potential-resummation boundary, fixed-complexity and normalization traps, and historical comparisons. I20's kinetic source scope and I23's introduction, H interface, resummation gap, cutoff stress tests, and final verdict were used. Existing statement/reading-contract JSON was inspected as an index, then the H source itself was read afresh. An overbroad contract-label filter incidentally displayed a few unrelated I20 statements before it was discarded; those statements were not used. No live sibling task outputs, shared acceptance indexes, or unrelated project trees were used as evidence.

## Primary literature actually inspected

BGSS arXiv:2008.10403v2 was opened at the primary HTML URL and read in the already-retained v2 PDF text under I20. The HTML numbering 25.2–25.4 corresponds to PDF §§6.2.2–6.2.4; HTML Proposition 25.3/25.4 and Lemmas 25.5/25.6 correspond to PDF 6.2.3/6.2.4 and 6.2.5/6.2.6. Read the process theorem, these passages and proofs, Theorem 10's statement, §8.1's clustering-recollision translation chart, and the **whole §8.2 proof**, including point 3. The cited point-3 proof was not left as an unread black box. Its time-factor argument uses a localized creation or clustering-time coordinate. That argument has not been shown to preserve H's sharper layered representation when the marked event is redundant. The microscopic proof's use of Proposition 3.3.1 was checked at its statement and the initial discrete-sampling derivation; that proposition's entire later proof was not independently audited.

BGSS arXiv:2201.04514v1 was opened at its primary HTML URL and its existing I23 text was read at §1.3, Theorem 1.3, and equation (1.19). This is the equilibrium process comparison and stationarity patching mechanism. No reading of its entire long-time proof is claimed.

DHM arXiv:2408.07818v3 was opened at its primary abstract page; existing I20 v3 text was read at Proposition 1.2, the main regular-interval contract, §1.4.3, Definition 4.3/Proposition 4.5, and selected §14 one-root estimates. H's imported/adapted DHM package is the stipulated input here; the entire 200-page DHM proof was not audited. Those excerpts do not supply a new marked shrinking-window theorem.

Fresh search queries and the two recent stochastic-kinetic title leads are delimited in the literature file. Only their primary abstract pages were read; no claim about their complete theorem scope is based on abstracts. No newly fetched full external source body was retained.

## Derivation checks

No numerical scans or simulations were run. Analytic checks performed:

1. Normalization: each factorial block contributes μ^{|π|} times c_{|π|}, hence O(μ) to the ordinary cumulant. Centered fourth moments use κ₄+3κ₂². No qualitative chaos statement was used at the fluctuation scale.
2. Endpoint uniformity: use zero pulses and a partial final slab, enlarge only merger-time domains, integrate free translations with displacement-independent birth envelopes, and choose one K for the finitely many slab prefixes. This derives the uniform moments used under time integration.
3. Moving two-pulse uniformity: keep the same full T graph class and fixed recorded labels, remove pulse placement restrictions in absolute upper bounds, and count segment choices by fixed polynomials. No growing pulse grid is introduced.
4. Selected ordered time: its fixed-rank simplex density is one nonnegative binomial term, bounded by the sum τ^{a−1}/(a−1)!, yielding at most a|J|/τ relative to the unmarked simplex. Energy/flux bounds are uniform in time values.
5. Remainder order: remove high complexity and variation errors at an assigned power first; then use fixed-size dominated convergence for cycles and the uniform size tail. This proves a qualitative common rᵋ→0, with no illicit quantitative cycle rate.
6. Integrated functional identification: uniform fixed moments justify Fubini and dominated convergence of mixed time-integral moments; no ε-uniform point sampling argument is substituted.
7. Exact current identity: finite-ε test values use the two actual particle positions. Signed-current integrability follows from telescoping. Slab resets add no artificial physical jump.
8. Cutoff amplification: for γ=7/3, α=μ⁻⁷ᐟ³ gives α^{1−γ}=μ^{28/9} and μ⁻¹α^{2−γ}=μ⁻²ᐟ⁹. Qualitative remainders cannot be inserted into this singular integral without an additional estimate.

## Attempts that stop

**Direct GRR upgrade.** Trees pay the interval length; cycle and initial-block contributions only give rᵋ. The resulting bound is proved in analysis §6. Its amplified remainder is uncontrolled. GRR itself is old and available.

**Collision-current marks.** Exact transport/current splitting pays drift tightness. Adding finitely many event marks would cost a polynomial in graph size on existing tree charts. A redundant marked contact has a determined time, so the proposed interval factor is unpaid. Giving it a fresh independent collision time silently changes the measure. Freely cutting it may lose powers of μ or sharp connectedness; those losses have not been repaid.

**Microscopic close-pair adaptation.** H's primitive type-A pair is freely parameterized and has the stated gain only with a velocity-volume restriction. Arbitrary two events in a tiny window require additional treatment of nonprimitive directed chains and disconnected seeds. An extension of the terminal-witness/cut argument looks plausible but was not completed with exact activities, union bounds, and summability. It is not asserted as a lemma.

**Restart BGSS independently in each slab.** The interface law is the evolved, correlated exclusion ensemble, not a new product activity. Replacing it by independent births destroys the sharp cumulant and centering problem. H resums selected independent factors inside an exact hierarchy; it does not resample the physical gas.

**Aldous from deterministic-time moments.** No stopping-time conditional estimates were obtained. A deterministic trajectory with random initial law does not supply a collision-current martingale automatically.

**Eliminate all cycles on a good event.** H's negligible connected cycle *measure* is a signed-expansion statement, not a bound for the event that the entire gas has no recollision. The discrepancy coupling compares true and pasted flows, not full gas histories to a globally tree-only process.

No attempt above is a counterexample to the prescribed gas. The five outputs recommend retaining the technical partials and commissioning a focused window/current closure only; they do not recommend a full-theorem acceptance gate.
