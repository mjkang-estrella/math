# expanded-corpus-r226

**No qualifying new solution. No new Lean packet. Zero credit requested.** `results.json` contains exactly the 20 reserved ID-keyed entries: nine exclusions and eleven parked targets, each with literal statement, provenance, source receipts, review depth, actual attempts, remaining obligation and Lean cost.

## Prior resolutions and exclusions

- **362843:** the source itself proves the horoconvex-domain gap conjecture (Khan–Tuerkoen, Theorem 1.2).
- **363022:** Tang–Wang–Wang prove the reserved spider family in the source itself; current v4 still leaves generalized 363023 conjectural.
- **363244:** [Inoue et al., arXiv:2505.07002](https://arxiv.org/abs/2505.07002) proves the torus classification; higher-genus Kochol examples are a different scope.
- **363419:** exact arbitrary-pair four-clause public Lean proof in Omega, integrated on 2026-11-02; literal endpoint read. See CANDIDATE.md and retained HTTP receipts. No local public-proof rebuild claimed.
- **363540:** source Theorem 1.3 resolves its edge-deletion conjecture.
- **363596:** [Zhao–You–Zeng–Zhang, arXiv:2607.15071](https://arxiv.org/abs/2607.15071), Theorem 1.11, gives triangular edges >= spectral radius, covering the substantive claim. Isolated-vertex wording supplies no credit.
- **363639:** [Fomichev et al., arXiv:2607.24217](https://arxiv.org/abs/2607.24217) announces nonextension, hence a negative answer. Its primary abstract was read, but HTML bodies were unavailable. This is an exclusion on prior-resolution evidence with an explicit proof-body gap, not an independent verification.
- **363906:** [Zhang–Yang, arXiv:2605.22808](https://arxiv.org/abs/2605.22808), Theorem 1 and Section 4, already prove the recurrence in a stronger range. The same work was flagged in r208 for 382304.
- **363595:** literal C5 failure quarantined as an elementary classical formulation correction, with no discovery credit or Lean work.

## Reproducible finite coverage

- Spanning sets: **175480** two-element subsets across k=1..40, using direct BFS; **2306675** sign-representative pairs across k=1..150, using a second bitset diameter implementation. Both agree on the overlap and with the conjecture. Sign representatives preserve the metric because negating either generator preserves signed sums. A pair must generate the mod-2 quotient, justifying the bitset solver's determinant filter. Runs completed in about 7.3 and 26.5 seconds. This route was stopped on finding the exact existing Omega proof.
- Forbidden orientations: all labelled four-vertex regular multigraphs at degrees **7..11**, totaling 280 graphs; **100902** maximal forbidden-list tests. Also **100** six-vertex and **1000** ten-vertex degree-7 multigraph samples, constructed as unions of seven random perfect matchings with seed 226; all **61600** list tests passed. These are sampled multisets, not distinct-graph counts or exhaustive larger-order coverage. Runs took about 1.2 and 27 seconds.
- Trail Trap: full minimax of **K3,3** and **K5,5**, all **16** and **48** oriented second openings after fixing the first move by symmetry. Both are second-player wins. States visited: 181 and 1257427. This only reproduces known cases; n>=9 remains uncomputed.

Other finite targets did not receive complete exact object enumeration. In particular, no generalized-spider expansion, finite-field hypersurface search, or independent oldXi/tiered-tree implementation was completed. No exhaustive-review claim is made for those targets. The unspecified polynomial/big-O analytic bounds cannot be refuted by a single finite sample.

## Evidence and limits

Exact corpus lines including trailing newline are retained in `inputs/<ID>.jsonl`. `provenance-with-statements.json` records chunk path, one-based line, chunk/raw/statement SHA-256. All listed original arXiv versions were fetched as HTML where available; the two 2406.15084 HTML versions returned 404. Current-body definitions and theorem statements were selectively read, with excerpts retained. Fetching every version is not a claim to have read every proof, cited paper or printed construction. Full construction-clearance gates remain incomplete for parked/ineligible routes.

Live registry heads and tree receipts are retained: Lean Pool `01db1d7049cf9668bda1e9e106875ee1278b43e6`, Omega tree `82ca796fa3d326df95fef9758103880b5987a5bf`, OpenAI math `4eaee87548250b2682affda7d05d947c05554bae`. Lean Pool's tree is complete; Omega and OpenAI recursive root responses are truncated. Their negative path matches cannot establish absence of proofs. The exact Bajnok artifact was fetched by pinned path despite this limitation. Live literature/citing-work searches preceded numerical work, but the full Omega check was completed after the initial spanning sweeps; that sequencing limitation is recorded rather than represented as full pre-search novelty clearance.

`receipts/` preserves unique timestamped HTTP bodies, headers, status, exact URL and SHA-256 without replacement. Search receipts are separate JSON files; search-002 was not persisted and is not claimed as retained evidence. The other retained search receipts cover live primary-source leads and citing work. No denied Crossref, Semantic Scholar, arXiv search API, ScienceDirect or DBLP endpoint was requested directly; incidental search-engine excerpts did not authorize reopening those hosts. No TLS verification was disabled, no challenge was retried, and no redirect to a denied host was followed. Downloads were read as inert data, never executed or extracted.

All writes were lane-local. No child agents, git operations, ledger edits, browser tabs, publishing or external messages were used. Python used `python3 -I -B` with real script paths. Numerical runs used `scripts/cap.py`: two-CPU affinity, CPU 120 s, wall 140 s, sampled 6 GiB RSS ceiling, MALLOC_ARENA_MAX=2. RSS monitoring is sampled/process-local, not a cgroup guarantee. All numerical runs finished; no solver is left running. No Lean invocation occurred.

This is a bounded investigation, not the several-hour, all-finite-route investigation requested in TASK. Unfinished work is stated explicitly; no global novelty clearance, exact new theorem, independent review, paper, or acceptance is claimed.
