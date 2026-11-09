# Held-candidate reopening review

Review performed 2026-11-04 UTC (2026-11-03 America/Los_Angeles). This is a review recommendation, not acceptance. Credit awarded: **0**. Root decides. No mathematical endpoint was rejected in this review.

| Priority | MathDB | Source/prior-art hold | Current recommendation |
|---|---|---|---|
| 1 | 330264 | **NARROWED** | **KEEP HOLD**: fresh capped replay incomplete |
| 2 | 352038 | **UNCHANGED** | **KEEP HOLD**: published A.5 status remains undetermined |
| 3 | 324342 | **NARROWED** | **KEEP HOLD**: fresh capped replay incomplete |

The first and third decisions distinguish the substantive source gate from the additional replay gate. Under the precedent in TASK.txt and rainbow-root-ruling-r1.json, their unread-body risks can be treated as qualified limitations at the source gate. I do not require those bodies to become readable as a condition of that qualified disposition. However, I cannot recommend an unconditional reopening with a successful fresh replay when the newly required replay has actually stopped at its resource limits. Root can use these source findings when arranging a compliant replay.

## Inputs and access record

Read TASK.txt in full first, then the three required AGENTS files, the ledger entries and listed candidate/review/dossier materials. Required-condition and parent-integration decisions were reconciled, including the superseding conference significance adjudication and journal-glyph clearance. Original artifacts remain unchanged.

The exact old URL/result enumeration is in **prior-routes.tsv** and **prior-routes.json**, with original receipt paths, including duplicated observations preserved by later dossiers. **prior-route-text-excerpts.txt** includes URL context from nonstandard/text receipts and source-comparison notes; **route-notes.md** records prose-only errors, inherited denials and routes that were intentionally never fetched. The JSON report groups the structured observations by candidate. These inventories are part of this report: their successes are not all full-body reads.

New direct requests are in **http-receipts.jsonl**: UTC, URL, final URL, HTTP status, content hash, bytes and lane-local fresh download directory. Search responses are in search-round2.json and search-round3.json; the first exploratory search is summarized in search-round1-summary.json, without claiming a saved raw response. The two new dated OpenAlex query failures are in openalex-web-attempt.json; no HTTP status/body hash is available for those web-tool accessibility errors. Search snippets, including unsolicited denied-host hits, were not opened as a workaround.

No denied route was retried. Excluded families include Springer, HAL content, ScienceDirect, JKU repository/SFB, Crossref, Semantic Scholar, arXiv search API, fatcat, scholar.archive, CiteSeerX, MathDB/Palomar and IEEE publisher routes. The old JKU double-403 lapse belongs to the frozen prior review, not this run. TLS verification remained enabled. A new zbMATH request returned403 and was stopped. Its unverified query identifier was not a valid exact-paper identification, so it provides no review evidence. No second zbMATH route was tried.

## 1. MathDB 330264 — Coxeter geodesic growth

**Old routes/results.** The coxeter-prefixed entries in the route inventory cover arXiv history/PDF versions, author lists/GitHub trees, institutional publication metadata, Crossref/OpenAlex metadata and inspected prior/later growth papers. Springer accessibility failure and HAL v2/v3 Anubis denials supplied no journal body. The fidelity review's versioned HTML returned404. MathDB/Palomar inherited403 was respected. Author and institutional listings authenticate bibliographic identity, not journal-body identity.

**New evidence.** Each previously unrequested version-specific abstract page was obtained once:

- arXiv:1504.02774v1: submitted 10 April 2015.
- v2: submitted 6 March 2016.
- v3: submitted 17 January 2020; its comment identifies a typo correction in formula (3).

See downloads/request-001 through request-003. I read Conjecture1.3 in the frozen explicit v1/v2/v3 text and the complete normalized v2/v3 extraction diff. All retain the three spectral hypotheses and equal-geodesic-growth conclusion. The changed formulas concern the adjugate numerator, not the conjecture. The 2020 author-submitted revision is after the 2016 journal publication. That is **positive post-publication retention evidence**, independent of an inference from a search miss. It does not prove that the journal text is identical or that every subsequent correction was investigated. No comment labels v3 an authenticated accepted manuscript.

The dated new OpenAlex citing query was inaccessible through the web tool and was not retried. New exact-conjecture/repository searches supplied no additional body establishing journal identity. Retain the frozen bounded McKay/Godsil/link-regular-growth comparisons and their limits; no fresh full citation-universe clearance is claimed. The newly checked OpenAI head is unchanged, so its earlier path screen remains a screen of that head. Omega has advanced; its current head alone supplies no new body/history clearance.

**Hold: NARROWED.** Under the stated precedent, the unread journal body can be a qualified limitation because the actual author revision retains the conjecture after publication. Remaining limitations: unread version of record; bounded and dated citing-body/registry screens; no worldwide priority claim; trust in imported upstream cache.

**Literal fidelity.** Independently recovered inventory chunk0003 line4740, retaining the exact raw JSONL line and chunk/line hashes in literal-bindings.json and 330264.raw.jsonl. Endpoint Conjecture quantifies trees on arbitrary Fin n/Fin m, equality of actual adjacency/complement/intrinsic-line-graph characteristic polynomials, and equality of every individual shortest-word count. Its negation uses the nineteen-vertex pair and a discrepancy at length18. This is within the literal universal claim. No new fidelity defect was found.

**Fresh replay.** Safely extracted the original full ZIP into a new lane directory; no bundled olean was imported and no author script was executed. Eight original modules compiled and each passed explicit-module leanchecker: GroupSemantics, NormalForm, TraceAction, AutomatonSemantics, WordCounting, MachineInvariant, SpectralDefinitions, ConcreteMachine. SpectralWitness was killed by the wall watchdog at **140s**, sampled peak **2,816,180KiB**, exit137. Endpoint compilation, its checker and a fresh endpoint #print axioms were therefore not reached. See logs/replay-330264.status and per-module build/check logs. Earlier successful endpoint audits are frozen evidence only, not a success of this capped replay.

**Recommendation: KEEP HOLD for the incomplete capped replay.** The source gate supports qualified reopening under the stated precedent; it no longer needs to be treated as an unqualified journal-body blocker. Root still needs a compliant successful final replay and its other packaging gates.

## 2. MathDB 352038 — distinct continued-fraction coefficients

**Old routes/results.** The expanded-corpus-r45 and continued-fraction entries in the inventory cover successful arXiv abs/v1/PDF access, official Elsevier core metadata only, Crossref/OpenAlex metadata and two body-read dispersion successors; registry subtree/body/history routes are preserved. Correct ScienceDirect and a separate incorrect PII returned403. JKU repository root returned403, SFB had verified-TLS failure and web502/timeout, JKU team metadata gave no manuscript. MaRDI and author/publication snippets link the old preprint; they are not mathematical publication bodies.

**New bounded investigation.** Exact-author/appendix, DOI/title and public-repository searches were made and saved. The new post-June2023 OpenAlex citing query failed accessibility, with no body read or retry. The version-specific v1 abstract was recognized as previously fetched and deliberately skipped, rather than counted as a new request. I read the cached abstract history: only v1, 23 September2021. There is no authenticated post-publication revision or accepted-manuscript identity in this evidence. The old specialist successor bodies concern dispersion, not a quotation retaining the coefficient-rank conjecture.

The 2023 Journal of Complexity76,101724 body remains unread. A changed title, bibliographic link to arXiv or the absence of another arXiv version cannot decide whether AppendixA.5 was retained, changed, removed or resolved. No conclusion about its status follows from unsuccessful searches.

**Hold: UNCHANGED. Recommendation: KEEP HOLD.** This is exactly the material undetermined-source-status case in the brief, and does not meet the positive-retention condition of the precedent. A lawful journal body, authenticated accepted manuscript, or actual later quotation establishing retained status could change the assessment.

The literal was independently rebound to chunk0008 line1359, saved as 352038.raw.jsonl. The frozen fidelity review establishes that the endpoint concerns distinct coefficients of a purely periodic quadratic integer, not multiplicities or only square roots. Its witness has seventh distinct value8 and 7·8>55. This review found no new fidelity objection and does not claim journal equivalence. No fresh Lean replay was needed or claimed for this non-reopened candidate. Preserve the r2 relevant-subtree/history characterization, incomplete global/citation coverage and imported-cache limitations.

## 3. MathDB 324342 — conference-matrix row code

**Old routes/results.** Conference-prefixed inventory entries include closed AG/GG metadata, CORE Scholar metadata, Gulliver home/journals lists, old citation queries, cited arXiv bodies and registry routes. fatcat timed out; scholar.archive returned proof-of-work; ScienceDirect403, HAL challenge and CiteSeerX429 were stopped; GG's OpenAlex citing query429 was not retried. Gaborit tables covered small fields only. AG Section2/Propositions2.1–2.2/tables and GG2008 bodies remain unread. The later r3 author-posted IEEE journal rendering already closes the EVY conjecture/glyph gap; this review does not reinstate it.

**New routes.** Gulliver's previously unrequested publications.html returned200 and lists AG bibliographically without attaching a body to its entry. Codetables.de root/nav/main returned200: its advertised classical linear-code tables have q≤9, so that advertised table domain excludes F19. A linked Harada–Munemasa public database returned200 after its normal redirect; its displayed categories are small fields/rings and it supplies no displayed F19 category. These are explicit scope observations, not proof that no F19 code appears elsewhere.

A new public Combinatorial Press PDF on codes from orthogonal designs was downloaded once (request-007). Its extracted text was empty; it was **not body-read or used as construction evidence**. Search excerpts are discovery leads only. No claim that this unread new paper excludes subsumption is made.

**Positive construction exclusion.** I read the actual cached Armario–Frau arXiv:1311.2637 §1.2, Propositions1.3–1.4 and Table1, with the surrounding attribution to AG. Their descriptions require nonzero α in [αI,W], or nonzero α,β in [αI,βI+W], and give length2n codes. For p=k=19 the first requires α²=0; the second requires α²+β²=0. The nonzero squares mod19 are {1,4,5,6,7,9,11,16,17}; −1=18 is absent. Therefore neither described construction produces the order20 F19 witness. Their unmodified length is40, whereas the witness row code has length20. I independently enumerated both congruences, checked the Gram matrix and rank10, and verified the weight9 combination using exact arithmetic; see independent-conference-check.json. These are ordinary checks, not replacements for kernel replay.

**Hold: NARROWED.** This meets the described-construction exclusion limb of the 388087 precedent. It does **not** exclude an uninspected AG remark or table concerning the length-n row code when p divides k. That precise risk remains a qualified limitation. GG2008 remains an unread low-risk existence/MDS-parameter source, not a cleared body. Preserve the incomplete citation/global-registry coverage.

**Literal and fresh replay.** Independently rebound chunk0002 line3870, saved exact raw line and hashes. The universal prime/order-p+1/row-code/MDS/dimension/distance statement matches Conjecture5's definition. Rank10 and a nonzero weight9 word refute MDS and the distance clause at p19; the dimension clause holds. No exact-d=9, minimality or classification claim is added.

R4 provides an unpacked source packet rather than a ZIP at the listed location. I created a review-owned source-snapshot ZIP of its exact main/audit/control Lean bytes and safely extracted it to a new directory; no prebuilt local objects or author programs were used. Main compilation with -M3500 was killed at the **6GiB RSS threshold** (sampled peak6,294,620KiB,28s; exit137). Its checker and fresh endpoint #print axioms were not reached. See logs/replay-324342.status and main build log. This establishes no mathematical failure.

**Recommendation: KEEP HOLD for the incomplete capped replay.** The prior-construction body risk supports qualified reopening at the source gate under the stated precedent. Root can apply that ruling after a compliant successful replay and the remaining manuscript/package gates.

## Integrity, resources and handback

inputs-before.sha256 and inputs-after.sha256 cover1,688 entries; integrity.json reports one whole-file change: **ledger.json changed concurrently**. This lane never wrote it. Preserved before/after candidate excerpts compare equal (ledger-comparison.json). All named candidate/review/dossier inputs, the corpus chunks, instructions, source pins and toolchain hashes checked unchanged. The initial broad snapshot followed introductory reads and preceded new retrieval/replay; it is not an assertion that hashing preceded the first read.

Every Python process used python3 -I through the lane's RSS watchdog, two-CPU affinity,120CPU/140wall seconds and MALLOC_ARENA_MAX=2. Every direct Lean invocation used -M3500 with the same wrapper, two threads and strict warnings; every checker named its module. Only one review-owned heavy process ran at a time. The watchdog samples process-group RSS and kills at6GiB; ordinary sampling can observe a small threshold overshoot. A harmless /proc-exit race warning in the first watchdog version was corrected for later calls. No limit was raised after a failure.

All writes, caches, temporary files, downloads and extracts are inside this lane. No child agent, git operation, browser tab, author contact, credential use, paywall bypass, shared-ledger edit, upload, publication or external message was performed. All review-owned processes have finished; no background job is left. Imported pinned core/mathlib/package objects remain trusted, not independently rebuilt.
