# fresh-corpus-r19 handoff

**Zero accepted credit. Two exact finite candidate refutations deserve follow-up; neither has a completed Lean endpoint.** All40 reserved literal statements have been inspected and preserved. No shared ledger, publication, upload, external message, browser tab, child agent or git operation was used.

## Strongest candidates

**338640, bicommutative minimum:** explicit1505-member maximal intersecting family of seven-subsets on15 points, against the literal source construction's1870 members at k=2. Full independent direct-set checks cover1,131,760 pairs, all6435 seven-subsets, and4930 explicit outside-set disjointness witnesses. This is a genuine maximality comparison, not merely an intersecting subfamily. `PROOF-NOTES.md` restores the source definition, Fano system, ten construction classes, quantifiers and source Theorem1 proof. `bicommutative-search.json` and `bicommutative-cover.json` retain the complete witness and domination certificate. No minimum-size or asymptotic claim.

**339278, positive Candy Nim splitting:** G=[12,20,24] is a strictly increasing P-position. The only positive sum=xor split of12 is4+8 up to permutation. Exact minimax values are V(G)=38 and V([4,8,20,24])=36. Independent sorted Windsor-take and labeled signed-score recurrences agree; the entire30450-state rectangular Bellman certificate is retained. This is beyond the excluded power-of-two/no-decomposition shortcut. The2025 published Question10.2 still asks the question, but its notation permits zero piles whereas MathDB explicitly requires positive parts. If zeros are permitted, [0,a] is a trivial unchanged game. Independent fidelity/significance review must decide the positive-parts endpoint; this is not a refutation of the permissive-zero wording. `PROOF-NOTES.md` gives the no-carry classification and Bellman induction argument.

Both candidates have bounded public prior-art searches with identified unread literature, not novelty clearance. Their construction/verification ease does not establish significance. Root alone can route further formalization and independent reviews; no acceptance is requested on present evidence.

## Lean status and residuals

The bicommutative definitions use actual `Finset (Finset (Fin 15))` objects, sourceFamily, seven-uniformity, all-pairs intersection, all-seven-subset maximality and strict size comparison. `lean/Attempt.lean` attempts the **literal** finite-set endpoint using kernel `decide`. It did not compile successfully. Initial failures were missing Fintype imports; the corrected direct attempt was killed, exit137/signal9, under60-second CPU /65-second wall caps,16GiB address-space and2048MiB Lean managed-memory caps. The precise cause of signal9 was not diagnosed; do not label it proof or infer infeasibility. Full error logs and exit receipt are retained. Error-recovery `sorryAx` in the failed initial log is a failing audit, not an allowed dependency or proved result.

A fresh, sanitized-environment **definitions-only** rebuild succeeds with strict warningAsError on Lean4.34.1 and pinned mathlibd13f23b723b8a846827a245b89c10fc7d3f11612. All7 local definitions/instances have transitive axiom outputs within propext/Classical.choice/Quot.sound. This checks the actual finite-set data and definitions; it proves **no** counterexample theorem. Receipt: `lean/definitions-receipt.json`; log: `lean/definitions.log`; fresh source: `lean/fresh-definitions/Definitions.lean`. Upstream prebuilt oleans are trusted, not rebuilt. No completed packet, paper, endpoint audit or acceptance replay is claimed.

Precise bicommutative next step: efficient kernel certificate soundness over the literal finite subsets, including lookup/membership/disjointness bridges and source ten-family identification. Precise Candy Nim next step: source game semantics, Bellman certificate soundness, legal winning-move characterization, permutation/zero deletion invariance, positive splitting classification, then exact table evaluation. These are substantive formal semantic tasks; Python arithmetic/table components are not equated with the endpoint.

## Other work and exclusions

339052 received two analytic frame-balancing attempts after actual Section5 theorem/proof inspection. Pair-column rotation preserves tightness but gives only stationarity; re-tightening a single column recovers the source Lemma5.5 identity. Neither implies equal norms. The missing step is a global volume-nondecreasing norm-balancing transformation or a strict separation from **all** equal-norm frames. No numerical optimizer is claimed to resolve it.

339210 is already resolved by Costa–Dalai arXiv2002.11025v1 Section3 Proposition1. Original Conjecture1/Eq26 and the full successor mass-transfer proof were compared.339263 is explicitly refuted in its own cited source1805.06171 Section3, k9/x3/n21 with7 labels against conjectured5.338792 and339174 already report counterexamples in their literal records; no primary-proof audit is claimed for those two.339279's max formulation appears routine from the source nonnegative-value bound and equal-pile games; no max/min wording change is nominated. Every other ID has an individual technical obstruction and next lemma in `results.json`.

Protected/held330264,335230,326640, active324342, palette332204, accepted388087/333569 and rejected337160 were not reopened. All39 historical families remain excluded. Reservation absence is not global unreviewed status; routing reviewed:false flags were not treated as reliable.

## Corpus and prior context

`results.json` is keyed by all40 IDs and includes the exact literal statement, source/canonical URLs, original corpus path, full chunk SHA256, original line number, raw-line SHA256 including the newline, review depth, status, residual, zero credit and no Lean-complete flag. `literal/{id}.jsonl` preserves each raw line byte-for-byte with its newline. `literal-receipts.json` is the concise provenance index. `literal-statements.txt` is only a human-readable derivative.

Ancestor instructions, both campaign ledgers, prior-campaign context, upstream pin/catalogue and recent r17 disposition were consulted. `context-pins.json` records hashes. A bounded historical search visited42638 summary/review/result/rejection/context/ledger-named md/json files <=300kB. The69 raw matches include numeric/hash substrings; after filtering,40 meaningful matches are the current ledger reservation list. No old substantive exact-ID note was located by that bounded search, which cannot clear title-only notes or global prior art. The initial rg scan respected ignored-directory rules and returned no matches; it was replaced by the explicit bounded scan and is not evidence of coverage.

## Registries, sources and reproducibility

Live OpenAI/math HEAD at2026-11-01T08:30:01Z is4eaee87548250b2682affda7d05d947c05554bae, unchanged from the user's08:24 receipt. Referenced r8/r10 complete-preprints-tree receipts were hash-verified and reused. `registry-screen.json` records the complete inherited path screen, terms and435 path hits (including broad substring false positives). It is **not** full proof-body clearance. The root recursive truncated tree was not treated as complete. Inherited MathDB/Palomar403 routes were neither retried nor bypassed.

`sources/receipts.json` records URLs, retrieval UTC, status and hashes for the original bicommutative/hashing/Candy Nim/cube/packing PDFs,2020 hashing successor, lawful2025 published Candy Nim chapter,2007 Kneser thesis and random-process primary manuscript. `source-versions.json` records inspected PDF header versions. Download does not mean full proof review: only the passages specifically named in `PROOF-NOTES.md` and `results.json` were inspected. Search queries/leads and limitations are in `search-receipts.json`. No new publisher denial was incurred; no hash for an inaccessible body is invented.

Replay the exact diagnostics with:

    taskset -c 0,1 timeout 90s python diagnostics.py
    taskset -c 0,1 timeout 115s python validate_candidates.py
    taskset -c 0,1 timeout 70s python lean/replay_definitions.py

The scripts themselves enforce2-CPU affinity, explicit CPU and memory caps. Diagnostics took about2.65seconds, independent finite validation about0.60seconds. Complete per-game splits and every counterexample are retained; the256-game scan found one nontrivial positive-splitting counterexample, with no hidden truncation. All experiments finished and tool sessions were reaped before handoff. `validation.json` records final integrity checks. This lane is a research dossier, not an unchanged self-contained completed proof packet.
