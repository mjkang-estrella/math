# Expanded corpus r183 — bounded research report

Lane: `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r183`.

No qualified new candidate; zero credit claimed. There are exactly 20 ID-keyed entries in results.json. Six targets have prior proofs/refutations; two admit ordinary arguments that fall under the brief's routine-classical-bridge exclusion; twelve remain parked with explicit scope, source or mathematical gaps. No Lean theorem was produced, and no dummy Lean packet is supplied. CANDIDATE.md contains the two complete ordinary arguments and the sustained unresolved promotion route. Root acceptance and independent review remain separate.

## Most useful findings

- **345906, C9 weak shuffle nilpotent kernel:** a block decomposition gives an ordinary full-scope proof using the classical shuffle polynomial theorem. This is a very short reduction from the source recursion to a classical algebra construction, with very high routine/source-ingredient credit risk. It is not proposed as a qualifying discovery. Full proof in CANDIDATE.md.
- **345919, natural orientation:** DFS tree edges down and non-tree edges up give a directed fundamental cycle basis. This is routine classical graph theory and is not proposed for credit.
- **346742, promotion:** exact cyclic-sieving checks agree through n=8, including all 315031552 linear extensions at n=8. No failure or uniform fixed-point formula was found. Positivity is already proved (Gatzweiler–Krattenthaler, Corollary 10). A January 2026 primary seminar abstract reports ongoing work on this precise conjecture; neither absence of a located final paper nor these computations establishes novelty.
- **346736:** Mabilat's 2025 Theorem 5.11 already gives irreducibles of length at least 3(p-1)/2 for every odd prime p, directly refuting a uniform p+K upper bound. No new family was searched or claimed.
- **345833:** the primary source contradicts the normalized record's claim that the general Schur-positivity conjecture was proved. The record also corrupts the root-order formula. Parked for source fidelity, not incorrectly declared settled and not refuted through a malformed paraphrase.
- **348030:** ternary squarefree witnesses are not counterexamples to an existential alphabet bound. The source's bare wording also allows a trivial unary-alphabet reading; that is a formulation issue, never credit. The meaningful general-pattern large-alphabet problem remains unhandled.

## Primary-source dispositions

Prior proof: 345733 (Carranza–Kapulkin Theorem 5.8), 346335 (Kalugin Theorem 4.2.7), 347256 (the source's own Theorems 3 and 4), 347303 (Ohsugi–Tsuchiya Theorem 5.1 and the current source's Remark 41), 347573 (Du–Lucchini–Morris–Spiga Theorem 1.1, September 2026). Prior refutation: 346736 (Mabilat 2025, Theorem 5.11). Relevant theorem/proof passages were read, with review depth distinguished in results.json; no independent audit of every cited proof ingredient is claimed.

Parked: 345825, 345833, 346036, 346180, 346181, 346182, 346742, 347085, 347368, 347738, 347807, 348030. The three enumeration-complexity claims are one family. The metric-graph and asymptotic claims do not admit a refutation by a single finite sample. The Latin-tableaux and consecutive-stack targets are adjacent to credited families, but this report does not equate them with the accepted targets merely from shared terminology.

## Exact computational coverage

All computations below followed the literature/citing-neighbourhood searches and live proof-registry screen.

- C9: all pairs of equal-length binary words for n=1 through 14 satisfy the source's strict leading-square sufficient criterion; at n=14, 16384 words and 134209536 distinct unordered pairs. A sweep of the maximum over earlier pairs also checks the source's three-word criterion. This is a bounded diagnostic, not a formal proof. The separate exact block-coefficient check covers 3969 ordered pairs, each input length 0 through 5.
- Promotion: Python enumerations at n=5,6,7; independent C rank/bitset enumeration reproduces the n=7 histogram, then exhausts n=8. At n=8: 112 orbits of length 16 and 6563120 of length 48. The polynomial modulo q^(6n)-1 agrees exactly with the orbit-character polynomial. Polynomial positivity was also diagnosed for n=1 through 40, without treating a known positivity theorem as a new result.
- Natural orientation: every labelled simple graph at orders 1 through 6, 33867 total, passes the directed fundamental-cycle construction. The same enumeration counts gap-free graphs, including 15034 gap-free six-vertex graphs without isolates. Their matching number is at most 3, a range subsumed by current published edge-ideal results; no higher-power Betti numbers or full invariant-extension search are claimed.
- Latin tableaux: every partition of area 1 through 18, every row-deletion subpartition tested for wideness, with an exact backtracking row/column Latin feasibility search on each wide shape. No obstruction found. At area 18 there are 385 partitions, 85 wide.
- Fertility: all six consecutive forbidden patterns of length three, on every permutation of lengths 1 through 8. First positive fertilities not observed in this bounded range are respectively 17,29,33,33,29,17 in lexicographic pattern order. These are not proved infertility numbers.
- Words: all alphabet-permutation representatives of ternary squarefree words through length 26 and quaternary squarefree words through length 12. The ternary length-25 printed example is reproduced (one canonical extremal representative at 25, none at 26); no quaternary extremal in the checked range. This is the P=XX subcase only, not the all-pattern statement.

Scripts, complete logs, cap receipts and exact outputs are retained. The C programs are compiled to lane-local shared libraries with the existing Lean toolchain clang, not installed software. The first compiler attempts failed because g++ and ordinary system headers were absent; their logs are retained. The final self-contained C builds and asserted replays succeeded.

## Registries and access limits

Live HEAD receipts: Lean Pool `01db1d7049cf9668bda1e9e106875ee1278b43e6`; Omega `9bd1fbf58f6746fb2e4ca8a3b201c15b11941eed`; OpenAI/math `4eaee87548250b2682affda7d05d947c05554bae`. The complete live Omega D5/Problems trees have 14018/1741 entries and are not truncated. Lean Pool's full tree, all candidates files and the actual `LeanPool/projects.yml` were fetched at its SHA. The root-level `projects.yml` path returned 404; tree discovery located the real manifest. Exactly eight repository-search queries were made, spaced eight seconds, all HTTP 200.

The public Omega WeakShuffleNormalization proof from the same Mammez source was inspected at its claim/result and relevant construction. Its normalization statement does not assert C9 reducedness. Generic algebraic-wheel/tableau/surname hits were not misclassified as target proofs. The sole repository-search hit for extremal/pattern/Lean was unrelated affine 013 extremal-counting metadata, not evidence for the all-pattern conjecture. These are bounded screens with actual relevant scope checks, not global proof clearance. Full details and receipts are in outputs/registry-screen.json and sources/.

Inherited denied routes (MathDB, ScienceDirect, Crossref and arXiv search API) were not retried. TLS verification remained enabled. A web fetch of the NSF-hosted Kreweras paper timed out; the ordinary arXiv primary-paper route succeeded. No account, browser, upload, message, git or child-agent action occurred.

## Limits and reproducibility

Every substantive numerical run used scripts/limited.py: 2 CPUs, per-process CPU 120 seconds, process-group sampled RSS watchdog 6 GiB, wall 140 seconds, MALLOC_ARENA_MAX=2, lane-local TMPDIR, and one heavy process at a time. No process was left running or killed/restarted in the background. The Python n=7 promotion run completed close to the CPU limit; no larger Python sweep was attempted. C n=8 finished in about 81 wall seconds with about 51 MB sampled group RSS. The final C9 replay finished within its cap. Sampled watchdogs do not guarantee capture of every transient RSS peak.

The initial copied metadata-extraction wrapper monitored only its direct process and did not explicitly set MALLOC_ARENA_MAX. It was corrected before mathematical searches, and extraction was replayed under the corrected group wrapper. The original receipt is retained; this is not represented as retroactive compliance. Metadata/network reads and small text conversions were not represented as numerical searches.

Raw corpus lines, including their newline, are in raw/. extracted.json and results.json retain original one-based chunk line, chunk SHA-256, raw-line SHA-256 and statement SHA-256. sources/*.receipt.json retain actual URL, retrieval time, status and content hash. outputs/artifact-manifest.json records final lane artifacts. No full upstream Lean rebuild, kernel proof, worldwide-priority certification, complete citing-literature census or source-version-by-version proof audit is claimed. The pass sustained two main finite routes (C9 and promotion), but did not meet the brief's aspirational several-hour duration; elapsed evidence and coverage are stated rather than inflated.
