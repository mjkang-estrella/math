# Expanded corpus r242

No new solution or qualifying candidate was established. No Lean endpoint is claimed. Exactly 20 reserved IDs have entries in `results.json`: 7 are ineligible because of prior public results or resolution already reported in their source; 13 remain parked. Root acceptance and campaign counts are unchanged.

The exact corpus lines, including their newlines, are preserved in `raw/`. `extracted.json` records one-based line numbers, original chunk paths, chunk SHA-256, raw-line SHA-256 and UTF-8 statement SHA-256. `results.json` retains these statements and hashes and describes actual review depth separately for each ID.

## Ineligible routes

- **341823:** The live public matroid correlation database already contains the 12-element ternary rank-6 example attributed to Eur–Renshaw and independently Huh in August 2026. Its pair counts are `(180,162,162,180)`. Recounting its public bases gives the positive-weight Rayleigh ratio `100018001/81018001 > 8/7`. This is a consequence of already public construction data, not a new result. See `public-matroid-check.json` and the receipted database.
- **342114:** Li–Qi, arXiv:2609.16181, Theorem 1, proves the reserved second-moment bound, with exponent `A = 12`.
- **342504:** Kodess–Lazebnik–Muzychuk, arXiv:2610.06735, refutes the prime-power conjecture with `D(25;3,6) ≅ D(25;3,18)` and an infinite extension-field family, while proving the prime-field case.
- **342585:** The source itself immediately states that Einollahzadeh–Karkhaneei completely confirmed its Conjecture 2. The unresolved MathDB gloss is unreliable here.
- **342681:** The cited Lü–Wu paper itself refutes the conjecture for all `n ≥ 4` and proves it for `n = 2,3`.
- **342764:** The cited source states that Guo already confirmed its Conjecture 1. The earlier confirming paper arXiv:1805.05808 was also retrieved.
- **342975:** Bodirsky–Starke, arXiv:2103.08625, Theorem 3.5, classifies the submaximal elements below the directed edge as `T₃` and the prime cycles, proving the reserved covering assertion.

These are source-backed dispositions, not independent Lean audits of those public results.

## Exact computational attempts

**341987, mixed-sign purely singular splitter sets.** Read the source definitions, Conjecture 3.1 and adjacent prime-power obstructions. A perfect splitter is an exact cover of the nonzero residues by injective multiplier blocks, avoiding zero. The unit splitter in the block covering residue 1 can be normalized to 1. Enumerating these normalized exact covers found no witness:

- Initial pass: 3,854 eligible triples with `4 ≤ k₁+k₂ ≤ 40`, `1 ≤ k₁ < k₂`, `m ≤ 2000`, `m > k₁+k₂+1`, correct congruence and pure-singularity conditions. There were 29,640 search nodes. The sole node-capped triple was `(k₁,k₂,m)=(3,4,512)`; it is not claimed excluded by this calculation.
- Extended pass: 870 further tested triples, targeting sums 31–60 and moduli at most 5000, stopped cleanly at its 105-second internal limit. All tested triples were unsatisfiable in the diagnostic search, with 34,011 nodes and no per-instance caps. The last completed triple was `(12,21,4225)`. This is only partial coverage of the requested extended rectangle: see the exact per-instance list, not the intended loop bounds, for coverage.
- `splitter-search.json`, `splitter-extended-search.json`, scripts and full logs make these checks reproducible. The extended pass overlaps the first pass; their counts must not be added as distinct instances.
- Yuan's 2022 work already treats multiplier sums 15–30. Leung–Zhang's 2026 proof concerns positive multipliers `[1,k]`, so it is not incorrectly counted as a resolution of this mixed-sign record.

**342815, Poonen.** NextClosure enumerated *all* intersection-closed families on labeled universes of sizes 1–5, without initially forcing the empty set or full set. Counts were `4, 14, 122, 4960, 2771104`. Full-ground separating families with the unique-low-frequency hypothesis numbered `1, 4, 9, 16, 25`; literal failures numbered `0, 2, 6, 12, 20`. Every failure omits the empty set. Under the intended normalization containing both empty and full sets, the surviving families are precisely the expected `n` families and there is no counterexample through size 5. An independent direct powerset enumeration verifies the totals and normalized assertion through size 4. The tiny example `{{b},{a,b}}` is an omitted-normalization failure and receives zero credit. See `poonen-search.json`, `poonen-literal-failures.json` and `logs/checks-known-v2.log`.

The source's Proposition 7 connects the intended result to two Poonen strengthenings. This is a substantial uniform gap, not resolved by these small-instance checks.

**342834, semicomplete digraphs.** Read the source's connectedness requirement for eulerian subdigraphs, Conjecture 7, cut obstruction and factor-merging setup. The citing paper improves the connectivity bound to `ceil((6k+1)/5)`, already settling `k ≤ 4`. With fixed seed 342834, the diagnostic generated 735 dense semicomplete digraphs on 8–13 vertices with deletion counts 5–8. Exactly 313 met the required `(k+1)`-arc-connectivity threshold, checked by every nonempty proper directed cut. For each, one randomly sampled set of `k` arcs was deleted. Exact subset dynamic programming found a Hamilton cycle in all 313 resulting digraphs, which is stronger than needed for those samples. No refutation. This is not exhaustive graph or deletion-set coverage. The exact graphs and deletions are retained in `semicomplete-search.json`.

**342025, shifted switching.** Read the actual switch, validity and hop definitions, Theorem 5.5, coplactic algorithm Theorem 4.2, the simple-decomposition discussion and Proposition 4.7. Coplacticity of the resulting tableau does not establish invariance of the number of local switches. A faithful generator/checker for shifted LR tableaux and representative changes was not completed, so no unreliable sweep is reported.

## Remaining parked targets

The other entries retain precise gaps: uniform LUBF counting (341981); regular fiber-cell closures (342021); unconstrained/directed KTV mixing beyond the publicly Lean-proved bipartite case (342145); general reductive-group scheme morphism beyond the source's GL_n theorem (342691); Robin gap and ratio comparisons in the stipulated parameter ranges (342761/342762); support uniqueness beyond mesh-mutation counts (342993); a uniform Boolean-dimension bound or unbounded family (343026); and a uniform positive cubic-vertex fraction in edge-minimal bricks (343113). A finite sample cannot refute an unspecified uniform constant or asymptotic bound. No dummy finite tests or surrogate Lean theorems were produced for these.

## Access, provenance and limits

- Read the three required AGENTS files, campaign ledgers, inherited context, upstream pin and manuscript catalogue entry point. A bounded exact-ID scan of historical reports and ledgers found only this lane's assignment, no older substantive exclusion; this is not a global historical novelty clearance.
- Literature/citing-work and GitHub/Lean Pool screens preceded exhaustive searches. Direct HTTP receipts are indexed in `http-receipts-index.json`. Web search responses 2–10 are retained; the first search has only an explicitly labeled manual summary. Primary source PDF bodies have separate URL, status, retrieval time and SHA-256 receipts.
- Live heads and recursive trees of Lean Pool, OpenAI/math and Omega were retrieved. Lean Pool's tree was complete; the other two recursive root trees were truncated. `registry-screen.json` is a bounded filename/topic screen, not exhaustive proof-body clearance. The public KTV Lean repository head was also retrieved.
- `source-version-inventory.json` records available arXiv version labels. The active splitter, switching, Poonen and semicomplete source papers each have one arXiv version. Current bodies were inspected for the other routes; all older versions of parked hard targets were not compared. No all-version or exhaustive citation clearance is asserted.
- Never contacted the inherited denied services; no 403/429 or challenge was retried, no denied-host redirect followed, and TLS verification remained enabled. Two acquisition mistakes remain preserved: a nonexistent abbreviated GitHub path returned 404 before the correct recorded head was used; a guessed arXiv ID downloaded an unrelated paper (`pdf-submaximal`) and was excluded from evidence, then the correct paper was located by search and retrieved as `pdf-2103.08625`.
- All numerical work used the lane-local resource wrapper: two CPUs, 120 seconds CPU, 140 seconds wall, sampled 6 GiB RSS and `MALLOC_ARENA_MAX=2`. One heavy process ran at a time. Peak recorded RSS stayed below 116 MiB. RSS sampling is not a cgroup guarantee. Initial C++ compilation could not start because no compiler was available; the actual Poonen calculation used Python. Failed attempts and successful replacement logs are preserved.
- Every Python invocation used `python3 -I -B` and a real script path for retained computations. Downloaded code was not executed or imported. No installs, git operations, child agents, shared edits, public messages, uploads or browser tabs. No jobs remain running. No Lean invocation or upstream rebuild claim.
