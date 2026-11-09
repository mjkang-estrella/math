# Expanded corpus r203

No qualifying new candidate; zero accepted credit. This is a bounded investigation, not a complete literature or proof audit, and it did not satisfy the brief's requested several-hour sustained pass. All 20 reserved IDs have explicit dispositions in `results.json`, with limitations preserved rather than converted into novelty clearance. No Lean endpoint or Lean packet was produced.

## Useful dispositions

- **373726:** excluded old statement. The latest arXiv v4 changes delta to delta-(k-1), requires prescribed cycle sizes, and prints the transitive-tournament obstruction. Refuting the obsolete bound is zero credit.
- **374723:** already refuted by Pant, in the reserved source itself.
- **367384:** source Theorems 2.6 and 2.9 assert the requested code parameters.
- **367448 / 376144:** one family, resolved by arXiv:2607.18122 Theorem 1.3.
- **357804:** Zhu–Hao–He arXiv:2404.12204 Theorem 1.2 gives uniqueness on a wider range; published in 2025.
- **363447:** full ordinary proof in `CANDIDATE.md`; excluded as an elementary classical linear-algebra bridge.
- **357547:** excluded by current public Omega manuscript Theorem 1.15, `CyclicMorphismAttractorMinimum.result`, at pinned HEAD 97f84965e06cc34e7073b503ed7e89ba816c860b. The full unrestricted original Conjecture 42 scope is explicit, including weak rotations and zero middle coefficients. Primary problem/manuscript/code bodies retained in `sources/omega-parry-*`. Upstream Lean claim not replayed locally. The separate arXiv:2511.00650 lead is not needed for this exclusion.

## Actual computations

All successful numerical jobs finished normally under `scripts/limited.py`, which sets two-CPU affinity, CPU 120 s, wall 140 s, process-group sampled RSS watchdog 6 GiB, MALLOC_ARENA_MAX=2, and lane-local temporary storage. Logs and resource receipts are retained. No Lean was invoked. Initial missing NetworkX and compiler failures are retained; NetworkX was copied from an existing campaign dependency into this lane, with no install. The attempted compiler launch found no compiler and performed no compilation. The C++ source was not executed; Python supplied the actual hypergraph searches.

- **370065:** fixed-distance maximum-clique search for all 12,376 seven-norm and 19,448 eight-norm alphabets drawn from the first 18 triangular squared norms, requiring the unit norm. Largest sizes remain 16 and 19. This goes beyond the source's single shortest-distance alphabet, but excludes sets with no unit segment or norms outside the listed alphabet, and does not classify all extremizers. `logs/lattice18.log`; smaller preliminary run in `logs/lattice12.log`.
- **382488:** all labelled 3-uniform and 4-uniform hypergraphs through 6 vertices, 1,082,420 cases total. Exact tables for phi=v-gamma are in `logs/hyper20.log`. In addition, 500 random greedy maximal families in each of six (r,s,n) regimes, 3,000 total: `logs/hyper-greedy.log`. No improvement found; no all-orders extremal upper bound established.
- **367979:** graph atlas through order 7, all 98 graphs satisfying the independent-set condition, with exact minimum cycle cover. Then 1,200 random graphs of orders 8–11, of which 443 satisfy that condition, also checked exactly. No violation. `logs/factors2.log`, `logs/factors-random.log`.
- **365542:** all unordered configuration pairs for all connected FS(X,Star_n) arising from atlas base graphs of orders 3–5: 11 base graphs, 57,687 pairs. Exact internally vertex-disjoint path count via max flow; no violation. `logs/fs5.log`. Runtime 117 s, normal exit.
- **374950:** maximum-clique checks for all n=2–5 and t=1–n, and n=6,t=3–6. All match the proposed size bound. Equality classification not checked. `logs/permutations-small.log`.

The analytic/infinite targets were parked with specific semantic or proof gaps. No exhaustive finite-group or non-realizable-matroid search was implemented. The program outputs are diagnostics, not Lean certificates.

## Provenance and access

`raw/` retains exact newline-terminated corpus records. `extracted.json` and each result retain chunk name, one-based line, chunk/raw/statement SHA256 hashes. Historical prose/results/ledgers were searched by exact IDs and titles; noisy digit-substring matches were retained in `history-matches.txt`. Structured inherited ledgers were parsed read-only and hashed in `outputs/context-audit.json`.

Every arXiv version listed on each of the 20 current abstract pages was fetched as HTML, with target passages extracted in `outputs/conjecture-passages.txt`. Downloading and extracting is not a complete proof-body review. Version-of-record checks are incomplete: the groups VOR and friends-and-strangers DOI landing were retrieved; several other publisher bodies remain unread or only have primary search metadata. No global current-publication claim is made.

HTTP bodies and dated status/hash receipts are retained in unique directories under `sources/`; the aggregate is `outputs/http-receipts.json`. TLS verification stayed enabled. No denied response occurred in the direct HTTP fetches. Inherited denied publisher/API routes were not retried. Web search coverage is bounded; not all tool-search results were serialized, so the transcript remains part of the search record.

`outputs/registry-screen.json` records Lean Pool HEAD, pinned projects/candidates downloads, eight spaced GitHub repository searches, noisy keyword hits, and the unrelated Coulomb-lattice search hit. Root recursive OpenAI/Omega tree retrievals are truncated and must not be treated as complete; separate scopes and their exact truncation flags are retained. No absence-of-proof claim follows from a path grep. No accounts, browser tabs, messages, uploads, git operations, shared edits, or child agents were used.

## Remaining work

The strongest parked computational routes are 370065 and 382488, followed by 367979 and 365542. None currently has a specific surviving obstruction or a complete proof mechanism. Any resumed route needs the remaining version-of-record/prior-proof scope checks before significant investment, then a literal general Lean statement and its proof or negation if an eligible endpoint appears. Root acceptance remains separate.

Validation: the shared maximum-clique routine agrees with independent brute force on all 1,024 labelled graphs of order 5; all 20 raw/statement hash checks pass (`logs/validation.log`). Complete registry scopes retrieved: Omega D5 25,648 entries, Problems 1,757 entries, OpenAI preprints 13,578 entries, all untruncated. Path matches alone are not proof audits.
