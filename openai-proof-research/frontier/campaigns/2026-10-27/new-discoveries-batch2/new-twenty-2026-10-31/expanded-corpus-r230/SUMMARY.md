# expanded-corpus-r230 research handback

**No qualifying discovery; zero credit requested; no Lean endpoint.** The packet contains exactly 20 reserved ID-keyed dispositions in results.json. Nine records are excluded from new discovery work, ten are parked, and one has a source-scope gap. Counts in the campaign ledger were not edited.

## Material exclusions

- **358657:** the LAWC G 2024 proceedings announce the MAX-VP NP-completeness result, including cubic graphs. This is a primary prior announcement; the full thesis reduction was not audited. Evidence: sources/lawcg24.pdf, around PDF text lines 1615–1650.
- **358874:** Antić, Glišić and Milivojčević, [2402.11044](https://arxiv.org/abs/2402.11044), already refute the geometric star-forest conjecture. Their paper was downloaded and the construction/result scope inspected. Do not confuse it with r224's different bounded-component question.
- **358949:** Li–Su–Fallat's source itself proves the matching-polynomial clause (Corollary 5.6) and supplies a disconnected 3-tree counterexample to the unrestricted characteristic-polynomial clause (Example 5.5).
- **359108:** the source itself refutes the Forking Path Conjecture, including its equivalent conflated-graph formulation.
- **359210:** Mao's identities are the source paper's proved Theorem 1.2, not an unresolved target.
- **359401:** Houshan Fu, [2610.06033](https://arxiv.org/abs/2610.06033), Theorem 1.2, already refutes Oxley's CCI conjecture at size 12 using the extended Golay matroid. The reserved source supplies the envelope equivalence. This recent October 2026 result was located before any matroid search investment.
- **359475:** Chung's 1988 theorem is precisely the connected-graph average-distance inequality. See [publisher statement](https://onlinelibrary.wiley.com/doi/10.1002/jgt.3190120213). Publisher abstract and primary later attribution were inspected; the full 1988 proof body was not retrieved.
- **358863:** a permitted relaxation of K(4,4) retains the source's printed Vámos restriction. The rank check yields Ingleton 15 < 16. This is an excluded source-ingredient/classical bridge, not a new significant result.
- **359777:** the elementary K4 family of all graphs with at least four edges has size 22 instead of the bound 20. This is an excluded small-parameter correction. It was not promoted to Lean.

The last two observations have full ordinary arguments in CANDIDATE.md and reproducible diagnostic checks. Neither receives discovery credit.

## Exact searches and mathematical effort

Literature and current registry screening preceded the searches. Source definitions were recovered first.

1. **Higher dimer covers, 358894.** Exact arbitrary-precision transfer DP for bounded order-reversing labelings of every fence through 17 vertices, m = 2,...,8: **458,752 cases, no dip**. First-sign symmetry uses order duality. A separate structured sweep tested **1,780 cases** at 24, 32, 48 vertices and m = 2,3,5,10,20, including long chains, periodic runs and seeded random orientations: no dip. Independent brute enumeration checked 189 small DP cases. Kang–Lei [2606.21923](https://arxiv.org/abs/2606.21923), §6, still lists the target as future work. Missing: a uniform unimodality theorem for the transfer operators, or a new finite dip. Numerical coverage is not a theorem.
2. **Odd seating couples, 359738.** Exact-cover search on all unit-distance multisets at v = 9,15,21,25,27. All **15, 120, 3,003, 293,930 and 203,490 lists**, respectively, were realized. Both 25 and 27 exceed the source's cited all-list verification through 23. The v = 25 and 27 runs completed within their caps (about 94 and 82 wall seconds). No failure, no uniform proof. The prime-order theorem and the even-order unit theorem do not settle this reserved odd-composite claim.
3. **PDO tagged partition congruences, 359085.** Exact truncated eta-product multiplication modulo 2^24 through argument 6,000: 4,008 / 2,000 / 1,002 / 998 checks for the four clauses; no violation. Direct multiplicity-weighted designated-part enumeration agrees through index 24. These are explicitly source-formula diagnostics, not potential credit for source-data failures. The first universally quantified clause implies the other three by substitution. The remaining task is uniform 2-adic coefficient divisibility.
4. **Two-component graph intersections, 359777.** Beyond the excluded K4 case, exhaust every labelled support graph H through seven vertices for the family containing all but at most s support edges, with s chosen maximally under λ3(H) > 2s. For n = 5,6,7 no such family exceeds the printed bound. At n = 7 this covers **2,097,152 supports** and all 301 three-partition cuts per support. This is not enumeration of all graph families. Unequal-weight or non-ball generator families remain open.
5. **Single relaxations, 358863.** Exact rank computation on the r = 4, t = 4 relaxation and its eight-element restriction confirms the routine classical obstruction; no large representability search was undertaken.

Logs and scripts are retained under logs/ and scripts/. A C++ prototype could not be compiled because g++ is absent; the actual sweeps used Python exact integers. No unbuilt C++ prototype is used as evidence.

## Parked targets and source limits

Each of the other records has a precise gap in results.json. In particular:

- **359145:** 2607.06336 enumerates Laplacian integral graphs through order 13. Its m = 3,6 and m = 2 counterexamples are not the reserved m = 1 conjecture. A new exhaustive graph generation beyond that published range was not run.
- **359598:** the source refutes stronger fixed-embedding/pseudotriangulation claims, not the abstract simple-graph conjecture. The distinction survives all source versions.
- **359660:** later strictly critical girth-6 constructions do not give bicritical girth-7 examples. Published small-order snark catalogues were screened; no fresh full snark enumeration was run.
- **359535:** the current source uses the exact Hamilton threshold and identifies floor(n/2) only for sufficiently large n. A small-order paraphrase failure would be zero-credit endpoint repair. No vertex-spread certificate was found.
- **359115:** the printed characteristic-zero conjecture is followed immediately by the source's assertion that this case follows from its interpolation theorem; the surrounding text discusses positive characteristic. This is a source-scope issue, not a newly solved dynamical conjecture.
- **358700, 359391, 359781:** the full optimization, arbitrary-set colouring and universal square-Kronecker support quantifiers remain beyond a concrete low-cost finite route in this pass. No artificial small-instance substitute or surrogate Lean theorem was created.

This is a bounded investigation, not several hours of exhaustive work on every record, not complete citation closure, and not global novelty clearance. Missing fresh searches are explicit rather than attributed to the lane as completed.

## Provenance, access and reproducibility

extracted.json gives every exact statement, original corpus path, one-based line number, full chunk SHA-256, raw-line SHA-256 including newline, and statement UTF-8 SHA-256. raw/ preserves all 20 literal lines. reservation.json is unchanged. inherited-read-receipts.json hashes the read-only ledgers/context; history-summary.txt distinguishes unrelated numeric/hash matches from actual historical reviews. Printed example/figure mentions from the strongest source families and all their versions are inventoried in printed-example-inventory.json.

All 20 current arXiv abstract histories and PDFs were retained. Earlier PDFs were also retained for every source with multiple listed versions. Receipt files contain UTC, requested/final URL, HTTP status, headers, bytes and SHA-256. Receipt files were created exclusively and not overwritten. Search responses are saved separately as sources/search01.json through search11.json; they are tool responses, not claimed raw HTTP receipts.

Current GitHub heads were fetched for OpenAI/math, Omega and Vilin97/lean-pool. Lean Pool's recursive path tree was untruncated; OpenAI and Omega trees were truncated. registry-path-screen.json records heads, truncation and lexical hits. A path-name search is not a semantic proof audit, and these limitations block any affirmative novelty clearance. No inspected match was promoted to a target proof without reading its statement. No source-only open label is used as evidence of novelty.

Denied services were not queried directly: Crossref, Semantic Scholar API, arXiv search API, ScienceDirect and DBLP. Search engines sometimes returned links on denied domains; those links were not opened. MathDB direct access was conservatively treated as inherited denied. No 403/429 retry, challenge retry, TLS-verification bypass, redirect to a denied host, browser tab, upload, git operation, child agent or shared-ledger edit was used. Downloaded material was stored in a freshly created lane-local sources directory and not executed. All Python runs used **python3 -I -B** and real script paths.

Every substantive numerical run used scripts/limited.py: at most two assigned CPUs, CPU 120 seconds, wall 140 seconds, sampled process RSS cap 6 GiB, MALLOC_ARENA_MAX=2. Monitoring is sampled process RSS, not a claim of cgroup-enforced aggregate memory accounting. One heavy process ran at a time. No computation remained running at handback. No Lean invocation occurred because no qualifying endpoint survived; no cache replay or axiom audit is claimed.
