# Independent counting and release-readiness audit

Audit snapshot: **2026-10-26 06:27:50 UTC / 2026-10-25 23:27:50 Pacific**. The campaign is being integrated concurrently; this report certifies the identified snapshot, not subsequent edits.

**Disposition: counting PASS for the existing 18 distinct accepted source outcomes; final twenty-outcome release HOLD.** There is no evidence of an inflated accepted count or an unsupported worldwide-novelty claim in the reviewed canonical presentation. Two further outcomes still require completion of the acceptance/release pipeline. The collector's integrity checks work on the current archives, but it does not itself establish the acceptance/replay facts asserted by its generated README.

## Scope and method

I read `openai-proof-research/AGENTS.md`, `sources/upstream.json`, relevant catalogue entries, the campaign README, ledger, outcome metadata and READMEs, source/provenance records, independent review records, and the packaging, archive-replay, and collection scripts. I inspected the separate premagic package in its own format. I compared the arithmetic source's actual Conjectures 3 and 9 and the saved duplicate/related source questions relevant to counting.

This is an independent cross-package accounting and delivery audit, not another proof-specific review. I did not rerun all Lean proofs, regenerate PDFs, extract archives, invoke Git, start agents, publish anything, or execute a build-writing verifier. Existing compilation, visual-QA, and replay results below are evidence inspected, not new executions claimed by this reviewer. ZIP contents were read in memory. SHA-256 calculations and consistency checks were independently rerun. The only file written by this audit is this report.

## Count and overlap

At the snapshot, `ledger.json` has `target = 20`, `verified_count = 18`, exactly 18 records, ordinals 1–18, and 18 distinct integer MathDB IDs. README's table and count agree. The arithmetic/rotation replay receipt is now present, so the earlier 15-plus-three-pending description has been superseded by evidence for 18 accepted outcomes.

| # | MathDB | Counted outcome and required scope label | Accounting |
| --- | --- | --- | --- |
| 1 | 336488 | Positive 3-by-3 premagic counterexample, non-diagonalizable over both R and C; new to project, worldwide priority unestablished | One. Shifted/scaled examples and larger dimensions add no counts. |
| 2 | 336487 | Dominant eigenvector's unnormalized norm claim refuted | One elementary literal-normalization correction. Different assertion from 336488. |
| 3 | 362146 | Zero/root-of-unity spectrum and zero iff nonpermutation for permutation-like matrices | One full source assertion; no worldwide priority claim. |
| 4 | 340783 | Fair-discrepancy propagation refuted at every positive tolerance | One formal verification of Patel's counterexample. |
| 5 | 354537 | Scaled Tepper identity for all source parameters | One elementary source-corollary proof; real-step strengthening adds no count. |
| 6 | 317856 | Monochromatic-box positive semidefiniteness | One known-result formalization; resolved in 2017. General Gram lemma adds no count. |
| 7 | 369281 | Four-card exclusion of 1/16 refutes the printed spectrum endpoint | One literal index correction, not a replacement general spectrum theorem. |
| 8 | 366458 | Four extensional signed-set fusion properties | One source outcome. No conventional-loop division or nonstandard-foundations claim. |
| 9 | 373182 | Continuous nonlinear Matkowski counterexample | One verification of Kiss's published result, not a new discovery. |
| 10 | 371201 | Normalized recurrence-orbit weight preservation | One verification of Patel's argument. More general recurrence parameters add no count. |
| 11 | 369280 | Exact quadratic eigenvector, eigenvalue 1/4, all n >= 3 | One known Tripathi consequence. Not the endpoint claim counted at 369281. |
| 12 | 349070 | Graph-normalization adjacency inequality | One standard majorization consequence; no iterative-convergence claim. |
| 13 | 372794 | Nonnegative coefficients for the actual source polynomial at every natural exponent | One known-result verification; prior posted proof and prior reported formalization credited. |
| 14 | 350342 | At least 38 distinct prime outputs refute the bound | One counterexample, not 38 outcomes. Source bound 13 and MathDB bound 10 are both refuted by the same witness. |
| 15 | 325243 | Free endpoint refutes the printed positivity-rigidity statement | One literal endpoint correction; no disproof of the intended truncated statement. |
| 16 | 375256 | Full simple arithmetic-function ratio inequality, all n >= 2 and k >= 1 | One source question in the joint arithmetic packet. |
| 17 | 375257 | Full mixed arithmetic-function ratio inequality, same parameter range | A second, different source question in that joint packet. |
| 18 | 368725 | Inactive-coordinate rotation refutes permutation rigidity | One smaller instance of Patel's known construction; no corrected-classification or trace-maximization claim. |
| pending | 327180 | Bernstein square-sum convexity, with symmetry/monotonicity/minimum corollaries | At most one additional outcome; known 2014 convexity result. |
| pending | 370245 | One rational witness refuting both Schur-stability operators | At most one additional outcome; specialization of Patel's posted family. |

### The arithmetic pair legitimately counts twice

The source TeX `arithmetic-ratio-lane/sources/arxiv/Lower_bounds_3.tex`, lines 172–177 and 233–241, has two different universal inequalities, labeled `Conjecture3` and `Conjecture9`. Their MathDB UUIDs are respectively `ac5f7206-dd68-4f1d-96b8-8b4418c0d3c5` and `5f14b71d-4034-4eb8-9e9a-0c6094139257`. Their final Lean declarations are respectively `ArithmeticRatios.mathdb_375256` and `ArithmeticRatios.mathdb_375257`.

The two released Lean modules are byte-identical, as are the joint papers. This is disclosed by both READMEs and both outcome records. Sharing a proof of the totient/psi/divisor-sum bounds and a paper is permissible under the requested **source-outcome** accounting. It is not evidence of two independent discoveries, two different papers, or 74 distinct proof declarations. Each ZIP contains the full joint module and paper, so neither release depends on obtaining the other archive. The independent arithmetic review and separate matching archive-replay records support both entries.

### Exclusions are correct and must remain explicit

- **318649 contributes zero.** Its saved statement and 366458 ask for the same closure, identity, unique annihilator, and commutativity properties, with renamed variables. `reviews/algebra-two.md` also identifies this duplicate. Neither the extra MathDB ID nor the four properties supplies another accepted outcome. The source's use of the word “loop” does not justify claiming the usual quasigroup division property.
- **327181 and 327182 contribute zero additional outcomes.** They concern monotonicity and the midpoint minimum of the same Bernstein square-sum. The packet groups them with 327180 and says `counted_outcomes: 1`. The minimum is already proved as Lemma 3.5 in the original source; the record's contrary historical wording is explicitly corrected in provenance. Global convexity, the sharp midpoint value, and the unformalized supplemental coefficient identity do not add counts.
- **370245 contributes at most one.** Two operators fail in one source question and one witness. Their two negations, the two spectral-radius calculations, and different parameter specializations are not additional source outcomes.
- The premagic/norm-one pair and the two shelf-shuffle questions share subject matter but have different source assertions. The norm-one witness is diagonalizable; the shelf spectrum correction does not prove the all-size quadratic eigenvector theorem. No duplicate is being counted in those pairs.
- The older R023–R041 papers are not added. The historical audit's 0/19 full-main-theorem formal coverage is kept separate from their written-proof status.

## Accepted archives: independent integrity checks

All 18 accepted ZIPs exist at the collector's expected paths. Each has exactly one `SHA256SUMS`, unique ZIP member names, no absolute or parent-traversal member path, exact manifest coverage of all non-manifest files, and matching SHA-256 for **every listed member**. I also checked for duplicate manifest entries. Every archive copy that has a corresponding canonical source file matches that file byte-for-byte.

All 17 standard-format packages include `outcome.json`, the full main Lean module, `main.tex`, `paper.pdf`, `review.md`, source/provenance records, rights/license files, dependency pins, the verifier, and build receipts. Each outcome's reviewed proof/paper hashes equal its current sources. Each existing proof audit is PASS at the current proof hash; each paper receipt has exit code zero, no reported issues, and the current TeX hash. This checks the documentary chain; it does not replace visual PDF review.

The recorded independent reviews contain the reviewed proof hashes for all 17. Fifteen also contain the current TeX hashes directly, including the later rotation/Ova documentation addenda. For **362146 and 340783**, `verification.json` records the original reviewed TeX hashes and the parent layout adoption. I located those exact original files and compared them with current TeX: changes are hyperlink styling, line/display wrapping of identifiers and hashes, and shorter equivalent MathDB URLs. No mathematical statement or proof changed. Those two are documented layout-only adoptions, not a missing mathematical review, although the `reviewed_paper_sha256` field is less precise than its name suggests.

The following are independently recomputed ZIP hashes. Paths are relative to `openai-proof-research/output/release/`; rows 2–18 are under `twenty-proofs/` with filename `<ID>-<package-name>-v1.zip`.

| MathDB | Package | ZIP SHA-256 |
| --- | --- | --- |
| 336488 | `premagic-diagonalizability-v1.zip` | `e26ec4d555342e7c00bb2e08b02af1c1a7d7bbf68854674dc0e0ab6eed1e30ad` |
| 336487 | norm-one | `42c1a5e86313c23f9b6046bc88f9249a1b3fe610596691f7160ccbb6d8ed631b` |
| 362146 | permutation-spectrum | `4634db5f6350128dc6577f9d2c9eef0ec04311fec116313d5c7ca2702900d637` |
| 340783 | fair-discrepancy | `c4686561a72ee14ff52c39800ea4f1563915d49e18df6fc8d61cd208df02c01a` |
| 354537 | scaled-tepper | `66ff10033b84d7076984f9c8e1df6d2a93ef74adfc0cfc1135a2590e25b56056` |
| 317856 | monochromatic-box | `c00a845f235efb4295d07af41abf80b46292db5c1c4567ed261b49b14ef9bcd0` |
| 369281 | shuffle-spectrum | `b87ca692f5d7371699aaf2466d905629167594c85b23e349e0493a6ac5bc69c2` |
| 366458 | sigma-fusion | `d0bfa9446c5b4b798b34d40bd4b2fccf2b7b32e2799f43b3428b60ce2c9755a6` |
| 373182 | matkowski | `ddf48985fe016c13128f63e6f87311924d3068b548d410c15c5c8cd0fe30c27b` |
| 371201 | fibonacci-weight | `af0c5c7ac81399134c1a51d3af5c78900d8d21435a44e249890a23afe5858d28` |
| 369280 | shuffle-quadratic | `12ddd5a4a5e1917159dbdeb07b0adecb2f2f43a27bf5bab80c8db1e717dcfbbf` |
| 349070 | graph-normalization | `83ad977324ba1e69e820efe0120576c7baf7785dbe825b6ac5ae265aab9ea23d` |
| 372794 | coefficient-positivity | `f7b2a636b3de5a08c346be60ce8ff761f4d54068a7a8ae0042953e4a8abcef17` |
| 350342 | ova-count | `51a25f05111db0dfbfd7c6bfe0145a49a84ec2e9fc11a2febd89451ca6722889` |
| 325243 | positivity-rigidity | `bc13a4eb5b88b30c1e8eac8d040b6a1f2709d68c384bc8fab9af7c0c4e835cfe` |
| 375256 | simple-arithmetic | `34fc98baef4614e7c18e748bd81a1264d6725594b3f835917d762dfadab10f17` |
| 375257 | mixed-arithmetic | `af8d30e952748c7c25104aabdd05318f1b10440fb352daf3a499ba9cf83a46b9` |
| 368725 | permutation-rigidity | `8a2b525a2071818821c12c08507bc87e1be080eac8717f14f4bf220dcc7c2b09` |

For rows 2–18, every ZIP hash equals both its ledger hash and a PASS record in the campaign's `build/*replay*.json` files; each replay proof hash equals the current main Lean source hash. This includes `build/arithmetic-rotation-replays.json` for the last three. The corresponding extracted replay logs and sources exist. These are 17 separate accepted archive records despite the shared arithmetic proof hash.

**Premagic is a supported format exception.** It contains `metadata.json`, `paper/main.tex`, `formal/Premagic.lean`, `notes/final-review.md`, `formal/rebuild.py`, `verification/verify_release.py`, `VERIFICATION.md`, and its own receipts, rather than the standard outcome layout. Its main proof and paper agree with the independent final review. The existing `build/release-replay/premagic-diagonalizability-v1/formal/build/audit.json` records a fresh 37-declaration compilation using the extracted source path; its source hashes agree with the ZIP. `VERIFICATION.md` records the extracted archive replay. Do not reject this package for lacking `outcome.json` or a root `verify_outcome.py`. Its omission of ledger hash/PASS fields is nevertheless worth fixing as described below.

## Collector review: blockers and hardening

`collect_release.py` resolves `PROJECT = ROOT.parents[3]` to the correct project root. Its special-case premagic path and the 17 standard paths are correct for the existing ledger. It reads the ZIP bytes once, checks their ledger hash when present, validates the complete nested manifest, and embeds those same bytes. Its outer `SHA256SUMS` covers every non-manifest outer file, including each nested ZIP, the README, ledger, and collection manifest. Fixed ZIP timestamps/permissions avoid incidental filesystem timestamp drift. The intended output is `output/release/twenty-proofs-v1.zip`.

I exercised the count gates in memory with a frozen ledger and all archive reads intercepted, so no collector output or receipt could be written:

| Input | Observed result |
| --- | --- |
| Real 18-entry snapshot | `Collection requires twenty accepted outcomes` |
| Twenty records containing duplicate IDs | `Duplicate source question` |
| Twenty distinct IDs, final records marked pending/FAIL for review and replay | Reached archive reading; no acceptance gate rejected them |
| Same input with target 999 and an invalid ordinal | Still reached archive reading |

**Release blocker: finish acceptance, not merely populate twenty IDs.** At this snapshot neither final candidate is accepted or archived. A final release must not be certified from a manually incremented count alone. The present script's generated assertion that every nested package was reviewed and rebuilt is supported by external workflow evidence, not established by this collector.

**Release automation gap: make the evidence binding explicit before treating the collector as a final acceptance validator.** Lines 19–22 enforce list length and ID uniqueness, but never inspect review/replay status, outcome status, source ID/main-theorem correspondence, or the presence of the promised paper/proof/review payload. Line 32 makes the ledger ZIP hash optional. In particular, entry 336488 has no `archive_sha256`, `replay`, or `independent_review`, so a replacement internally consistent premagic ZIP would bypass comparison with the accepted archive. Supply its hash above and explicit review/replay evidence; require all twenty archive hashes and matching PASS evidence. For the standard layout, bind the archive's verified outcome and reviewed proof/paper hashes to the ledger; retain a deliberate equivalent adapter for premagic. A manually documented final check can supply these facts, but the current collector alone cannot certify them.

**Minor defensive hardening:** require integer IDs, ordinals exactly 1–20, `target == 20`, and an allowed/explicit package path. The current code takes only the basename of `package` for standard archive lookup, so a misspelled directory with the right basename can go unnoticed. Also reject duplicate manifest lines, unsafe/absolute paths, symlink members, and unexpected top-level roots. ZIP duplicate names are already rejected, but manifest duplicate lines are silently collapsed into a dictionary, and traversal/symlink/root checks are absent. No such defect was found in the current 18 ZIPs. These are safeguards against future malformed artifacts, not evidence that existing archives are unsafe.

After assembly, independently read back the outer ZIP, check its complete member manifest, require exactly twenty nested archives and twenty matching IDs/hashes, and retain the final archive SHA-256. The collector writes a receipt but does not read back and verify its final output. No collection ZIP existed at this snapshot, and this audit did not create one.

## Remaining work for twenty

1. **327180 Bernstein:** during this audit `reviews/bernstein-shape.md` arrived with PASS for exactly one complete source outcome. It independently checked all 20 declarations at proof hash `a28d1890152b55dd274c1124677da0bf5b509afa4e7b5a8e9f50831e9def7801`, and TeX hash `d3af82702ea89fc1fbb563e7ae00777389eb089efafc7235cd084dfaa2732c5d`. Those equal the current canonical files and successful build receipts. `outcome.json` still says candidate/pending integration, no released ZIP exists, and there is no archive replay. Integrate the review, address its provenance-path/version-link notes, preserve the one-count/no-novelty/supplement-coverage labels, confirm final PDF QA, seal, package, and replay before adding entry 19.
2. **370245 Schur stability:** the implementation arrived during this audit, replacing the initial worker-building state. The canonical packet has a 77-declaration PASS compile receipt at proof hash `1c9c3eb6834dfdb0ae068e822e689415aa472fbe7677b97fea28327b9e4d516d` and a successful paper receipt at current TeX hash `4c5e3e37096111ea97c06ff445347065f0142fce55bf9e79f78c973957c7d722`. It remains candidate, with independent review pending; neither a released ZIP nor replay exists. Its self-review is not the independent review gate. Obtain the assigned independent verdict, integrate any fixes at reviewed hashes, confirm final PDF QA, seal, package, and replay before adding entry 20. Keep the scope at the literal positive-semidefinite-B conjecture and the one rational specialization; do not claim the full posted parameter family was formalized or count the two operators separately.
3. Reconcile final README/ledger/statuses and the collector evidence binding above, then assemble and independently verify the twenty-package delivery. No further source question needs to be invented if these two qualify. Neither is accepted merely because its compiler receipt passed.

## Provenance, rights, privacy, and minor documentation

**No blocking rights/privacy issue found in the 18 accepted inventories.** They contain original proofs/prose, short source records, attribution, and licenses; they do not bundle complete third-party paper bodies, raw multi-post discovery dumps, downloaded tools, dependency trees, or unrelated profile records. The source rights are explicitly reserved. Public solution author names/IDs are used for attribution. Absolute local paths and the local author's name occur in receipts; they are expected reproducibility metadata, not credentials. A targeted scan of archive text found no obvious private-key, bearer-token, or project-key pattern; this is not an exhaustive secret detector. Preparation does not authorize external posting.

I independently reconciled the accepted source/provenance SHA-256 references against retained local sources, including full MathDB snapshots, versioned manuscript HTML/PDF/TeX, and historical arithmetic receipts. The fair-discrepancy prior-body hash matches the body inside its retained MathDB response. Premagic's six source-manifest entries all match. Bernstein's twelve source-hash entries match its retained lane files; Schur's four source hashes in `metadata.json` match its lane files. Missing source bodies *inside a distributable ZIP* are intentional rights-conscious exclusions, not missing Lean dependencies: source reconstruction may require retrieving the cited version, while theorem replay requires the included Lean source plus external pinned compiled dependencies. The trust boundary remains the Lean executable and supplied mathlib dependency artifacts; this audit did not rebuild those dependencies.

Minor documentation items, distinct from the two pending acceptances:

- **Stale `NEXT.md`:** its headline says 9/20 and later sections say 11, 12, and 15; its last pipeline update still says drain the arithmetic replay and append 18. README/ledger currently say 18. Replace the accumulated active-state narrative with one unambiguous current checkpoint, or mark the older sections explicitly historical. Do not let a reader infer a completed 20 from the plan.
- **Copy-pasted attribution on 362146:** its ledger `priority`, `outcome.json` novelty field, and README discuss the separate fair-discrepancy/Patel construction. Its own paper correctly identifies the permutation-like theorem and makes no worldwide claim. Remove the unrelated sentence and keep a theorem-specific no-priority label.
- **Misleading snapshot paths/claims:** scaled-tepper and monochromatic-box READMEs say the packet contains source snapshots and `paper/main.tex`, then say full source bodies are not redistributed and the paper is `main.tex`. The ZIPs confirm the latter. State “versioned source references and hashes; full bodies retained in the development lane.” Bernstein's review identifies similar lane-relative paths that need explicit reference roots. Several historical manifests also inventory unrelated discovery filenames; these names/hashes add noise but do not ship those files or add outcomes.
- **Layout adoption terminology:** for 362146/340783, distinguish the original independent-review TeX hash from the current layout-adopted TeX hash in metadata. The existing `verification.json` provides that distinction; the generic `reviewed_paper_sha256` name obscures it. No new proof review is indicated by the inspected layout-only diff.
- **Historical statuses and bibliography:** retain the corrected-source warnings for the arithmetic record's unrelated older references, the Ova 10-versus-13 distinction, known 2017 monochromatic-box resolution, known 2014 Bernstein result, and other prior-proof credits. Frozen MathDB `open` fields do not establish current unresolved status. I found no supported reason to promote any of these packets to a worldwide-first discovery or first formalization.
- **Pending Schur metadata:** its `metadata.json` includes development `paper/main.tex`/PDF hashes and a development engine receipt, while the canonical paper and campaign build receipt now have another TeX hash. The README labels historical lane paths; continue distinguishing that historical build record from the current canonical reviewed/released bytes during integration, as already done for arithmetic provenance.

**Final audit conclusion:** the existing eighteen have consistent source-outcome accounting and intact reviewed/replayed delivery artifacts. The arithmetic pair is legitimately two source outcomes; the grouped Bernstein corollaries and signed-set duplicate add none. Completion remains conditional on the two identified final acceptances and a final evidence-bound twenty-package release check.

## Parent completion addendum

After this independent audit's eighteen-outcome snapshot, the final Bernstein and
Schur-stability proof reviews passed. Their current papers were visually inspected,
packages sealed, and exact extracted archives rebuilt successfully. The final
ledger has twenty distinct IDs. Their review and replay records are included.

The parent repaired the collector issues identified above: it now requires target
and count20, integer IDs and exact ordinals, mandatory accepted hashes and PASS
review/replay fields, valid canonical paths, verified archive metadata, required
proof/paper/review payloads, current proof/paper hash binding, and matching extracted
replay evidence. The premagic format has an explicit source/review/replay adapter.
Duplicate manifest lines, unsafe paths, symlinks, and unexpected roots are rejected.
The complete outer collection is reopened and verified after writing. Nine invalid
acceptance-record cases were independently exercised and rejected.

The copy-pasted permutation-spectrum attribution was corrected, the two earlier
layout adoptions were explicitly labeled in metadata, and the Tepper/box README
source descriptions and paths were corrected. Their four regenerated archives
passed fresh extracted-source rebuilds; updated hashes are in the final ledger.
`NEXT.md` is now one completed checkpoint rather than accumulated active snapshots.

The parent independently read back the final outer archive and all twenty inner
archives, checked every member hash, required twenty distinct IDs and accepted
metadata, and verified the index links. See `delivery-verification.json` and
`collection-verification.json`. Final collection SHA256:
`072f1ba954e4d31c5a9e3a5c82193bcfc4ab46828b425bb87296decc10a594b6`.
This addendum records parent integration and verification; it is not represented
as a second independent mathematical review or a new literature-priority audit.
