Research lane r186 — no eligible discovery submitted

Lane: /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r186

The 20 reserved IDs have individual dispositions in results.json: eight excluded routes and twelve parked routes. Zero new accepted results; no campaign count changed. No eligible strong candidate, ordinary full-scope new proof, or Lean endpoint was found. CANDIDATE.md records the rejected elementary permanent obstruction and the strongest unsuccessful search routes.

Primary-source findings

- 338783: the source's own Section 5, Theorem 28 disproves its Conjecture 19 with an eight-vertex 4-representation and a multiflow obstruction. This is already in arXiv v1.
- 339420: McGuinness, arXiv:2601.17624, Theorem 1.5 proves the rainbow-circuit result. The 2025 CanaDAM programme already announced it. The theorem and decomposition proof section were inspected; this is not a new result.
- 340078: rationality is proved in arXiv v2 and the 2020 version of record, Theorem 2 and the transfer-matrix proof following Theorem 14.
- 340108: the exact full-scope matching claim is Theorem 2.3 of the 2025 SLC article. Its proof applies the explicit cancellative-operation construction in Lemma 2.1.
- 338187: the same author group's 2023 IIIT research poster reports a regular but nonrecoverable T(5,5)(2,2) pattern. The poster was downloaded; a full independent algebraic replay was not performed. That prior report blocks novelty investment.
- 340021: the doubling conjecture appears in v1--v2 and is removed in v3--v5. Excluded under the brief's withdrawal rule; no claim that removal itself establishes truth or falsity.
- 338189: A={0,1}, d=2 gives exactly three permanent values, contradicting the printed exact bound four for every prime p>=5, including the published version's sufficiently-large-prime wording. This is an elementary constant-size formulation failure and is recommended for zero credit. No Lean resources spent on it.
- 350227: the apparent general finitary resolution arXiv:2501.04321 is withdrawn. The target is parked, not marked solved. Nonfinitary counterexamples do not dispose of this finitary claim.

Sustained computational routes

339243: generated every avoiding permutation through n=18 for representatives 123,132,231,321, covering all six patterns by inverse/reverse-complement symmetry. The generation inserts the unique largest entry and checks only newly possible occurrences. Each representative had exactly Catalan(18)=477,638,700 permutations at n=18. Counts match the source table through n=12. All growth inequalities 2 C_n <= C_(n+1) <= 4 C_n hold for n=3..17. Counts for n=18 are respectively 22,132,112; 17,593,170; 9,213,420; 13,948,966 (see validation.json for authoritative exact values). An independent factorial enumeration through n=8 validated the generator. These are bounded non-findings, not a proof of the conjecture. Full logs and resource receipts: logs/cycles16.*, logs/cycles18-*-fixed.* and logs/cycles18-{132,231,321}.*.

338558: for all 299 pairs n=2..24, 1<=l<=n, tested the source's cyclic-band graph and conjectured rank using the Jacobian of the selected entries of UV over F_1009. Every trial reached full row rank (additional trials permitted if necessary). Such a minor certifies the characteristic-zero generic-rank upper bound for that finite instance; the dimension count supplies the matching lower bound. No general theorem or kernel certificate is claimed. Deterministic seeds and complete output: scripts/ranks.py, outputs/ranks.json, outputs/ranks13-24.json, logs/ranks12.*, logs/ranks24.*. Replay ranks.py without arguments for n=2..12 and with arguments 13 24 for the extension.

339956: ultimately excluded: the source Corollary 3.7 plus Bolognini--Sentinelli arXiv:2605.24732 Theorem 4.2 (May 2026), whose statement and proof were read, already refute the universal inclusion through the published failure of Simon extendable shellability. Before this final citation follow-up, exact forward closure under the source's three decomposability operations, followed by recursive chordality checks, found no counterexample for (n,d)=(5,3),(5,4),(6,5). Closure sizes were 812 of 1024 clutters, 32 of 32, and 64 of 64. All 812 generated (5,3) clutters were chordal; there were 55 nonchordal clutters among all 1024. This does not give coverage at larger sizes. Source operations and checker are in scripts/clutters.py; output in outputs/clutters.json.

338657: exact maximum-clique search on nonempty subset compatibility graphs for n=1..8 found maxima 1,2,3,4,5,7,11,14. Witnesses were independently checked. A finite family cannot refute a bound with an unspecified constant c. No superlinear construction emerged. See outputs/bisection.json and scripts/small.py.

338189: all nonempty subsets of F_p for p=2,3,5,7,11 at d=2 were enumerated to document the elementary literal failure, after literature and registry screening. See outputs/permanent.json. This is a rejected correction, not a strong lead.

Registry and provenance

All 20 raw corpus lines are preserved byte-for-byte including their newline, with one-based line numbers, chunk hashes, raw hashes and statement hashes in outputs/provenance.json. All 41 posted arXiv version PDFs for the twenty source records were retrieved; their hashes and conjecture excerpts are in outputs/source-version-audit.json. Reading depth is explicit per result: fetching or excerpting a version does not imply a complete proof audit.

Lean Pool HEAD was fetched via /commits/HEAD: 01db1d7049cf9668bda1e9e106875ee1278b43e6. The pinned LeanPool/projects.yml and all ten candidates/ blobs were fetched and searched by identifiers, author names and title keywords. An initial root projects.yml request returned 404; the tree identified the actual nested path. Eight GitHub repository searches, spaced eight seconds apart, returned zero items. They were identifier-plus-lean metadata searches; this is not exhaustive code/author/name coverage or novelty clearance. Omega and OpenAI/math live HEAD receipts were also preserved, but no exhaustive live proof-body screen is claimed. outputs/registry-screen.json records queries, exact heads, hits and limitations.

Historical ID/title/arXiv searches in sibling SUMMARY/CANDIDATE/results/ledgers found administrative or incidental numerical/hash matches, not an inherited mathematical exclusion for a reserved ID. Both campaign ledgers and inherited context were parsed read-only and copied locally. No shared files were edited.

Limits and audit caveats

The twelve parked entries are unresolved, not certified novel. This pass did not complete the brief's aspirational several-hour deep programme or a small-instance implementation for every source-faithful finite target. In particular no staged-tree ideal enumerator, universal list-assignment solver, cop-game solver, Potts local-view LP, or refined-tree-index symbolic checker was implemented. Exact remaining semantic and mathematical gaps appear in results.json. Some versions of record remain unread; no missing-access clearance is claimed. The source-access gap rule was used to park those routes rather than manufacture semantic surrogates.

No Lean invocation or leanchecker run was made, and no Lean packet is warranted without a surviving eligible result. C and Python computations are diagnostics. Compiler failures from missing host headers are retained. An initial n=18 C run failed from an array bound of 18; arrays were enlarged to 32, that failed output was discarded, and all successful n=18 runs plus independent small factorial checks used the corrected program. No capped command was restarted after a maximum timeout. Resource receipts record two CPUs, CPU 120 s, wall 140 s, sampled process-group RSS 6 GiB, and MALLOC_ARENA_MAX=2. Only one heavy process ran at a time; all processes finished. Watchdog sampling is not a cgroup guarantee. TLS verification stayed enabled. No browser, account, upload, author contact, external message, git, or child agent was used.

Deliverables: results.json; SUMMARY.md; CANDIDATE.md; outputs/registry-screen.json; outputs/provenance.json; outputs/source-version-audit.json; outputs/validation.json; reproducible scripts, full logs, and dated HTTP body/status/hash receipts in sources/.
