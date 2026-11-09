# Expanded corpus r239 handback

**No qualifying new solution or literal Lean endpoint was found.** Exactly 20 ID-keyed dispositions are in results.json: five excluded as already resolved, one blocked by an explicit prior refutation announcement, and fourteen parked unresolved. This is a bounded research pass, not worldwide novelty clearance or a claim to have solved any reserved record.

## Decisive literature findings

- **346206:** the source itself disproves Chang–Roussel in Section 4 for r >= 7.
- **346257:** Jaume–Pastine–Schvöllner, arXiv:2103.00618, Theorem 3.9 proves the unicyclic transition statement.
- **346477:** Bani Mostafa A.–Ghorbani, arXiv:2005.06308, Theorems 3(i),6 prove the odd-start cycle labeling statement. Schroeder's 2024 correction expressly preserves that result as Theorem 3.1; the broader classification's correction does not reopen this record.
- **346708:** Yang's own source, Theorem 2.3, proves the real-rootedness statement.
- **346735:** Mabilat, arXiv:2404.10521, Theorem 1.1(i), proves finiteness over all finite commutative unital rings, including Z/NZ.
- **346440:** Funk–Matthews–Mayhew, arXiv:2510.00139, announces an infinite-group definability counterexample, while explicitly withholding its proof pending another structural theorem. Recorded as a prior announcement, not an independently verified full proof.
- **346309:** the intended invariant is perfect-matching index, not ordinary edge-chromatic number. A Vizing-based literal-paraphrase correction earns no credit.

## Actual finite work

- **346024:** all 400,995 choices of three exceptional elements outside [0,8] in Z/144 were covered at n=12,k=3. The three consecutive lexicographic batches assessed indices [0,119864), [119864,239146), [239146,400995). Of these, 399,267 failed exhaustive exact-cover complement search and 1,728 already had complete residues modulo 12; no timeouts. An additional 6,000 seeded random samples at k=3,4,5 gave 5,984 negative complement searches and 16 already-correct residue samples. No counterexample. This is a finite restriction only.
- **346524:** 600 biased random partial squares at orders 9,10,11,12,14,16 all received independently checked completions. A second search covered 5,550 samples across 37 source-reduced cases in types (a),(b),(c),(d),(f),(g),(h), orders 9–19: 5,506 checked completions, 44 indeterminate timeouts. No noncompletion was claimed.
- **346057:** rational grounded-Laplacian calculations covered all 625 ordered rooted unitrivalent shapes with 1–7 branch vertices (orders 4–16), and a prefix of 42 shapes at 8 branches (order 18). No equal matrices for nonisomorphic abstract trees. The diagnostic uses the nonlazy chain; Definition 4.1's fair holding coin divides every covariance matrix by 2, preserving equality comparisons. No source-to-Lean semantics claim.
- **345989:** 5,222,952 heuristic moves and 436 restarts sought a 3-page embedding of the 42-vertex, 126-edge Ec(K7). Best residual: 24 same-page crossings, independently rescored. This is neither a layout certificate nor an impossibility proof.

Full outputs and per-process resource receipts are in logs/. Numerical scripts use the lane-local resource wrapper; there was one heavy process at a time. Every run finished normally within 120 CPU seconds / 140 wall seconds, on two allowed CPUs, with sampled RSS far below 6 GiB. The wrapper's RSS monitor is a sampled process monitor, not a cgroup or transient descendant-memory guarantee.

## Provenance, access and limits

The three specified AGENTS.md files, current campaign and inherited ledgers, prior context and accepted/excluded-family instructions were read. No ledger counts were changed. Exact raw corpus lines, including their newline, one-based positions, chunk/raw/statement SHA-256 hashes are preserved in raw/ and extracted.json. Historical rg matches, including incidental numeric-substring matches, are retained in history-matches.txt. RESEARCH.md distinguishes source statements, theorem/proof reading, attempted mechanisms and remaining gaps.

All 19 distinct primary arXiv sources were fetched with dated URL/status/hash receipts. Every version listed on their current abstract pages was separately mirrored as a PDF; versions.json records the list. Current and promising-source definitions and relevant proof bodies were read. This does not claim complete side-by-side proof review of every historical version, every figure, every cited work, or every inaccessible journal revision. Source-contexts.json inventories textual conjecture and example/figure contexts. No counterexample advanced requiring complete visual construction clearance.

Live GitHub heads and registry trees, Lean Pool's projects file and candidate files were retained. OpenAI/math HEAD: 4eaee87548250b2682affda7d05d947c05554bae; Lean Pool HEAD: 01db1d7049cf9668bda1e9e106875ee1278b43e6; Omega HEAD: b5559d15a71bac88357aece33a357d0fa343b094. Main OpenAI and Omega recursive trees were truncated; the separately fetched OpenAI preprints subtree and Lean Pool tree were not. No exhaustive proof-content clearance is claimed. Eight direct GitHub repository queries returned zero hits; the dated queries and expanded author/arXiv/ID grep are in outputs/registry-screen.json. Initial live registry and GitHub web screens preceded computation; direct repository API queries were completed later, a chronology limitation explicitly retained. The ertwro 1/3–2/3 attempt at ccd4b3e7b3f6ab9fb94e6f9350852b2f13ba8229 admits a main-path sorry. No incomplete repository is classified as a proof.

HTTP bodies and receipts are in sources/; web-search records are in receipts/. The first general web-search response was not serialized locally; its primary-source findings were subsequently fetched and saved. No receipt was overwritten. TLS verification remained enabled. No request was made to the denied Crossref, Semantic Scholar, arXiv search API, ScienceDirect or DBLP endpoints. Search engines incidentally returned snippets from some denied domains; those pages were not opened. No 403/429/challenge occurred in the lane's direct HTTP fetches, so no denial was retried. No downloads were executed; PDFs were treated as data. No browser tabs, child agents, git, installs, uploads, external messages, or edits outside this lane were used.

CANDIDATE.md records the ranking and why nothing advances. No Lean run, dummy endpoint, sorry-based theorem, new axiom or acceptance claim was produced. The exact-solution goal remains unmet; unresolved targets are parked with their gaps rather than represented as solutions.
