# expanded-corpus-r201 research disposition

No qualifying new candidate and no accepted credit. All 20 reserved IDs have individual entries in results.json: 12 exclusions (11 prior results/bridges and one routine symmetry deduction) and eight parked unresolved targets. The campaign count was not changed. No strong new endpoint survived, so no Lean packet, compilation, leanchecker run, or independent formal replay is claimed.

## Sustained routes

**323000, hard-square denominator multiplicity — parked.** Recovered Conjecture 1.5 from both arXiv versions. Source computes periods through circumference 22. Implemented an independent-set row transfer compressed by the full dihedral action, followed by Berlekamp–Massey over F_1000000007. Covered every even circumference from 2 through 28. For n=24, 26, 28, respectively: 103682/271443/710647 row states, 2359/5536/13201 orbits, 801/1001/1001 scalar coefficients, inferred recurrence degrees 57/91/95. The inferred polynomial is square-free at n=26; at n=24 and 28 its repeated-root part has degrees 3 and 1, with no triple-root factor. These are finite-prefix modular diagnostics, not characteristic-zero denominator proofs or guarantees for all m. Exact integer transfers through m=20 independently validate the implementation for n=2,4,6,8,10. See outputs/squares-summary.json, outputs/squares-validation.json and full logs/squares*.log. The main gap is uniform cancellation/multiplicity control; no counterexample was found.

**354340, Bruhat orbit interval — parked.** Read the latest source's definitions, vertex-transitivity theorem, stronger proposed orbit maximum and membership proof. Built undirected reflection graphs using the actual strong Bruhat order; graph edges include all transpositions, not only covers. Exact anchored graph-isomorphism backtracking resolves all 120 intervals in S5. Of 719 examined S6 intervals (lexicographic indices 0–718), 718 have complete orbits and satisfy the conjecture. One interval has 69 vertex-isomorphism checks unresolved after the internal time budget; index 719 was not examined. This is not a complete computational S6 verification. A separate subword-interval generator tested 60 seeded Bruhat-irreducible S7 examples with 8–11 inversions and interval sizes 80–220, all with complete orbits and no failure. See outputs/bruhat-coverage.json and the detailed bruhat JSONs. Remaining gap: prove that arbitrary identity orbits are principal lower ideals, beyond the source's known membership of the proposed maximum. No finite Lean certificate arose.

**349324, Panyushev duality — parked.** Confirmed the source's full five-property formulation and the classical/exceptional distinction. Enumerated all 105 F4 antichains: rowvacuation is an involution but eight antichains fail cardinality reversal, as the source already warns. This does not refute existence of another involution. A natural compatible construction in the exceptional types remains missing. See outputs/f4.json.

**323625, kernels — parked.** Exhausted all 4096 labelled loopless digraphs on four vertices and all 59049 labelled oriented graphs on five vertices, using directed simple paths and directed distances to absorbing sets. All eligible quasi-transitive cases have the required kernel. Exact k-specific counts are in outputs/kernels-*.json. These small cases largely duplicate known k=2,3 or order-trivial regimes; they do not solve the general k>=4 problem or earn credit.

## Exclusions

- 322999: live public Lean necklace-period theorem plus the source's own Theorem 7.6 already implies the reserved denominator claim. Do not promote the same bridge.
- 328588: McNew's actual Theorem 2.2 proof and following paragraph establish reciprocal convex/extremal-prime convergence. Tutaj's published revision acknowledges the work.
- 354073: the cited Chern source itself proves the exact statement as Theorem 1.3, equation (1.7), with proof in Section 3.3.
- 354633 and 354634: Yang arXiv:2404.01973, Theorems 1.1 and 1.3/Example 4.4 prove the full identities.
- 358955: Xia arXiv:2609.08816, Theorem 1.2 equation (1.13), proves the exact Li–Wang conjecture.
- 367479: public Omega PopStackSimple.result proves PopStackDefs.claim, the exact Fibonacci enumeration. The definitions, endpoint and proof structure were read; no local replay is claimed.
- 373846: the pinned OpenAI Boone–Higman manuscript Theorem 1.1 is the exact target, accepted as true under the ancestor instructions.
- 374680: source-cited Lin–Liu–Liu–Liu–Xin arXiv:2601.09551 explicitly proves Pons–Batle as Conjecture 1.2 following its Theorem 1.1.
- 375694: the source itself reports the Kim–Park list-square counterexamples.
- 381151: the source itself identifies the signed-path claim as equivalent to the known Four Color Theorem.
- 365147: complete equal-radius fibres are complement-invariant; the explicit transformation preserves complement pairs. This gives the target in a few lines and is a zero-credit routine bridge. See outputs/ZCURVE-ROUTINE-BRIDGE.md. Earlier campaign screening of this family was retained.

## Other parked targets

356182 needs an actual natural decorated-map bijection, not equal coefficients or a lexicographic pairing; the generating-series identity is already known. 363775 needs the full q-statistic-preserving tree/Dyck-path correspondence; q=0 is already proved. 367923 is the precise ideal-circle-pattern four-way infinite equivalence, not the preceding circle-packing result; later related papers remain incompletely read. 368974's source already verifies all 21078 4-connected planar graphs through order 13; no new Speyer invariant computation beyond that range was implemented here. These are honest gaps, not claims of global openness or novelty clearance.

## Provenance, registries and limits

Exact newline-preserving raw corpus records are in raw/; extracted.json and every result entry give chunk name, one-based line and chunk/raw/statement SHA-256. Original arXiv landing pages, every listed original version PDF, and followed primary sources have timestamped URL/status/header/byte-hash receipts in fresh sources/ subdirectories. outputs/version-audit.json records versions and text hashes; adjacent-version text diffs are retained. Downloaded versions were not all audited page by page. Actual target definitions/statements and the specifically named theorem/proof passages were inspected. Literature/citing-work searches are retained in outputs/web-search-01.json through web-search-09.json. Citation coverage is bounded and incomplete.

Live /commits/HEAD: Lean Pool 01db1d7049cf9668bda1e9e106875ee1278b43e6; OpenAI/math 4eaee87548250b2682affda7d05d947c05554bae; Omega c0fde349a1ec3243a8af5fe63c37c1dd48866b1b. Lean Pool projects.yml and all nine candidate files were fetched and text-screened. Complete live Omega D5 and Problems path trees contain 14054 and 1757 entries; the root recursive trees are truncated and are explicitly not complete coverage. Eight spaced GitHub repository queries returned 200. Query coverage does not include every author/name/ID combination, and no authenticated code search or all-proof-body audit was performed. OpenAI's unchanged HEAD permits reuse of its cached complete preprints path catalogue. See outputs/registry-screen.json.

Yang's publisher route returned 403 at Wiley; receipt retained, no retry. Other version-of-record checks are partial: Cambridge and Numdam primary bodies and Springer record were obtained; author/arXiv manuscripts substitute where publication bodies were not independently read. Inherited denied ScienceDirect/Crossref/arXiv-search routes were not retried. Missing access is never novelty clearance.

All heavy searches ran sequentially under scripts/limited.py: two CPUs, sampled process-group RSS watchdog at 6 GiB, CPU 120 seconds, wall 140 seconds, MALLOC_ARENA_MAX=2, lane-local TMPDIR. Full stdout/stderr and resource receipts are in logs/. No search was killed by the outer cap. Internal Bruhat limits are recorded rather than hidden. Compiler discovery failures and one initial structured-script error are retained, followed by successful corrected runs. No Lean invocation occurred. No background work remains.

Work duration is shorter than the brief's suggested several-hour pass. Coverage is limited to the explicit bounds above, with no claim that all requested future deep work or inaccessible primary literature has been exhausted. The evidence supports a no-candidate handback, not a solved reservation or global novelty survey.
