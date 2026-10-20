# T088P133 manuscript round 1 — implementation report

This handoff is a complete mathematical manuscript **DRAFT**, with formal integration pending. It is an implementation, not an independent correctness, contribution, formal or manuscript review, acceptance-ready package, portable release or publication. Count remains **18/20**. No gate is self-assigned.

Author: **Myeongjin Kang**, no affiliation or contact details. Assigned runner: Codex / GPT-6 Astra / high / default service tier. No nested agents were used. Publication, uploads, submissions, contacts and browser UI remained STOPPED. All task writes, downloads, temporary files, builds, renders, copies and controls are confined to this new manuscript root. No git command, staging, commit, old-author/review/parent/ledger mutation or active-formal-root access was performed. Preservation evidence is described below; this is not a syscall-denial claim.

## Result and mathematical scope

`packet/public/main.tex`, `references.tex` and `witness-tables.tex` produce the 17-page PDF `packet/public/output/pdf/main.pdf`, entitled *Projection-body volume for four-dimensional polytopes with at most six facets*. The frozen theorem is unchanged: every convex four-polytope K with nonempty interior and at most six ACTUAL irredundant facets satisfies V4(Pi K) <= (160/3)V4(K)^3 for h(Pi K)(u)=V3(K|u-perp), with equality if and only if K is a simplex. Every exactly-six-facet case is strict, including nonsimple, repeated-Gale, zero and boundary strata.

The operative source mathematics at pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` is stipulated true. This task did not conduct an upstream truth audit. The draft provides the full geometric maximum and attainment, actual-facet normal distinctness and nonzero-middle exclusion, complementary determinants/coarea/Gamma/factorials, signed Laplace normalization, log-concavity and conditioning hypotheses, survival integration with boundary terms, the universal two-bracket algebra and strictness, signed partial fractions, exact coefficient identity, all zero/repeated-knot strata, minimum-facet classification, affine invariance and simplex equality. The coverage map is `packet/public/COVERAGE.md`.

Appendix A supplies all **248 nonzero sparse coefficients across ten patterns**, definitions, derived author algorithm and the pure positive endpoint monomials that survive repeated rates. It also derives and credits the later independent competing-phase reconstruction as verification of the original operation, not a changed theorem or original author derivation. The original partial-fraction route remains explicit. Exact support supplements the analytic and geometric proofs; it does not replace them. Floating geometry is diagnostic only.

The optional method-limit discussion distinguishes the separate exact corner formulas establishing auxiliary n>=5 failure from a negative coefficient, which only rejects that coefficient certificate. It makes no geometric claim in dimensions 5–8, no >=7-facet or general-body theorem, no full Brannen solution, no optimal auxiliary constant and no positive all-n threshold claim.

## Authentication, reading, attribution and rights

All supplied author and correctness-r3 anchors matched, as did the adopted contribution anchors. Every manifest payload authenticated: 24 author, 37 contribution and 48 correctness-r3 files (109 total). `private/input-authentication.json` records the initial results. The original frozen-scope hash is `86e1f30e2c867215026b2a4c2bc0c50144660618c486d2b2029e044bfce8d354`; the original proof hash is `971506a4ea3de75a883da6d0eced6b11b0b997cc2a6598c2e0487ee5a6e2bc84`. The other complete original anchors are in `packet/public/PROVENANCE.md` and the private authentication record. They were reauthenticated after implementation.

All user-required author, parent and review files were read in full. The contribution reading-limit file is actually `packet/public/reading-limits.md`; its private evidence is actually under that completed root's `private/`, as its authenticated manifest specifies. The correctness witness JSON was decoded in full and every polynomial tuple displayed in compact form. The original crosscheck code was read and retained privately; its round-2 interpolation dependency was not transplanted or rerun. AGENTS instructions, acceptance rules and the actual CONTENTS088 entry were read. The initial broad filename-only AGENTS search and truncated unrelated catalogue/ledger output are disclosed; no complete read of those unrelated contents is claimed.

Actual primary/source bodies were read to the recorded extents, not inferred from summaries: full SourceP main.tex/README/references, including facet/affine/simplex labels; FHLXv1 TeX introduction/preliminaries and all Section4; Prékopa1973 Theorem3 and Theorems6–8 with proofs; specified Saroglou opening/conclusion and v2 main-statement sections; r132 R1–R4/star report/notes; narrow I43/r112 and full r131 history. Eight retained SourceP/Petty bodies independently match the pinned complete tree's Git-blob hashes and sizes, computed without git. FHLX PDF was byte-authenticated only. Klefsjö records are metadata/abstract reads only; the primary bodies were not read. Brannen/CFLXX bodies remain unavailable. Other classical bodies not acquired/read are named as such; needed operations receive direct proofs or precise usable references.

`packet/public/source-reading-records.json` and `private/reading-register.json` record source-byte hashes and exact read extents. The private copies of completed acquisition/read registers retain actual versioned URLs, hashes and failures. No new global literature search was performed. The only new download was the pinned build engine and its ordinary TeX support cache. PQ1–PQ5 and the bounded class/search positioning are in the manuscript. Credit is allocated to SourceP interfaces, FHLX Section4, earlier r132 geometry/star, classical HNBUE/Laplace/reliability background and only the assessed new joint assembly. “No antecedent found in recorded reads” is not a first or worldwide-priority claim.

The adopted independent SUBSTANTIAL disposition was conditional on correctness; the subsequently adopted full unchanged-scope correctness PASS discharges that condition. These are attributed prior dispositions, neither acceptance nor an independent review of this manuscript. Earlier provider/network/usage failures were not mathematical verdicts. The earlier checker corrected a missing Vandermonde factor, and its successful spot samples were distinct-only, not full prior proof checks.

Chronology is preserved candidly. A proof sketch and exact certificate existed before the recorded freeze at 2026-10-20T17:21:32Z; the freeze preceded extended prose, not all ideas. Author FINAL reports sealing at 17:31:58.711847Z, while notes describe drafting/packaging at 17:36–17:45Z. These conflict; no preferred exact chronology is selected. Late companion/acceptance reads and the earlier temporary `/tmp` history-list deviation remain disclosed in Appendix B and PROVENANCE. Those historical deviations are not silently erased or repeated here.

Original paper/prose, PDF and manuscript renders: CC BY4.0. Original code: MIT, with full license and actual copied notices retained. The four copied support artifacts match their original bytes and hashes in `support-origin.json`. All third-party source/primary/history bodies and their derivatives stay private/local under original rights, outside the public payload and any future portable release. Copying establishes neither reading nor redistribution permission. Build engines/caches retain upstream rights and are outside the manuscript payload. See `RIGHTS.md`.

## Reproduction and actual outcomes

The following commands were run from this draft root (equivalent absolute paths were used in some invocations). They operate on new copies and outputs only:

```sh
python3 -B packet/public/support/reproduce.py build/checks
python3 -B packet/public/support/independent_certificate.py build/checks/rebuilt-witness.json
cmp packet/public/support/certificate-witness.json build/checks/rebuilt-witness.json
python3 -B packet/public/support/author-certificate.py > build/author-certificate.log
python3 -B packet/public/support/geometry_control.py > build/geometry-control.log
bash packet/public/build.sh
python3 -B packet/public/support/qa.py .
pdfinfo packet/public/output/pdf/main.pdf
pdftoppm -r 120 -png packet/public/output/pdf/main.pdf packet/public/renders/page
pdftotext -layout packet/public/output/pdf/main.pdf build/main.txt
pdftotext -bbox packet/public/output/pdf/main.pdf build/bbox.html
python3 -B packet/public/support/integrity_controls.py . work/integrity-controls
```

The reproduction driver compared all five polynomials (Np, NP, Den, D, T) for each of ten patterns between the original author construction, independent recurrence and retained witness. All match. The independently rebuilt complete witness JSON is byte-identical. All 248 displayed nonzero T coefficients are positive, minimum 2; each pure endpoint coefficient is verified. The universal cleared two-bracket identity is the zero polynomial in six independent variables. The n=5 coefficient control has minimum -6; the *separate* rational auxiliary corner ratio is 5495618760267/5255309886352 > 1. Full results and original-copy logs are in `packet/public/qa/`. The author main routine's Monte Carlo diagnostic is labelled as such. The geometry copy tested 40 generated six-facet examples, maximum displayed normalized ratio 0.999891; this is neither exhaustive nor proof evidence for untested strata.

Environment: Python3.14.7, Poppler26.01.0, Tectonic0.17.0 Linux x86_64 musl. The official engine archive and binary hashes are pinned in `bootstrap.py` and `private/tool-acquisition.json`. All XDG/cache/config/data/tmp outputs are redirected inside this root; compilation uses `--untrusted --keep-logs --keep-intermediates --reruns 2`. An initial read-only cache-path query displayed a pre-existing global path; its directories predated the task, and compilation used the local redirected cache. The local cache inventory records 415 files. This is not a fresh offline portable-toolchain release test.

A fixed `SOURCE_DATE_EPOCH=1792454400` is used for reproducibility. Its PDF metadata date is 2026-10-20 UTC (displayed October19 in PDT), not an asserted drafting/sealing chronology. A repeated build from final identical source and the same populated cache produced identical PDF bytes: SHA-256 **b6e27af10b3a4bd70a2392066fe14c5fdd02558001eff6b4ef2c3790a228bf95**. The PDF is **151280 bytes, 17 letter-sized pages**, unencrypted, no JavaScript. `qa/reproducibility.json` states the precise scope.

## PDF layout QA

The available PDF skill was applied; its create marker ran once before authoring. First compilation found two overfull paragraphs, twenty hyperref math-heading warnings and three underfull bibliography lines. Filename wrapping, displayed variable order, plain-text pattern headings and ragged-right references resolved those observations. Final log checks report **zero overfull boxes, zero underfull boxes, zero undefined or duplicate references, zero missing citation keys, zero LaTeX/package/hyperref warnings and zero missing-character reports**. The raw final engine log, console and exact check results are retained in `packet/public/qa/`.

Every one of the 17 final page images was visually inspected through `view_image` at 120dpi, including every formula page, all coefficient-table pages and both reference pages. After the first full inspection, unused small-table header groups were removed and continued tables labelled. Pages12–16 were rerendered and reinspected; pages1–11 and17 were PNG-byte-identical to the already inspected pages. The later repeat build produced the identical PDF. No clipping, overlap, unreadable table entries, missing visible references or black-square glyph defects were observed at that inspected scale. `qa/visual-inspection.json` records a separate observation and final image hash for each page. This is implementer layout QA, not independent manuscript review.

Supplementary bounding-box extraction found no extracted word outside the MediaBox on any page. The raw pdftotext bbox XML contains four XML-illegal control characters (codepoints18–21); they were removed only from the parser input, not the PDF or raw extraction. This disclosed text-geometry check supplements, and does not replace, visual glyph inspection. See `qa/bbox-qa.json`.

## Preservation and artifact integrity

The whole completed author/contribution/r3 roots and five exact parent disposition/adoption inputs were snapshotted before substantive implementation. The after comparison found all **1046 entries unchanged**, including path sets, file hashes/sizes, modes, hardlink counts and symlink targets. Old copied-control symlinks were recorded without following them. Eleven supplied/adopted anchor files and seventeen retained original bodies were rehashed successfully; the four copied support files still match original bytes. `qa/original-preservation.json` gives the result; full snapshots and end body checks are private/local. This does not claim full-body reading of all snapshotted files or absence of mutations by syscall tracing.

The verifier SHA-256 is **559b66d1a87c0273c7ecdc51bbff02b5b4589217c276ba44cfd6d3a10ab04d91**. `verify.py` requires externally supplied FINAL/MANIFEST/outsideREPORT anchors. It checks exact file and directory sets, sizes, SHA-256, modes, regular single-link payload files, safe relative paths and no symlink ancestry/payload. It performs no payload execution, build, network operation, cache write or report write. Mathematical correctness, rights, novelty, formalization and acceptance are outside its verdict.

Twelve separately sealed copies of the full then-current payload exercised intact verification, wrong external anchor, modified/missing/extra payload, extra empty directory, symlink, hardlink, mode change, and changes to MANIFEST/FINAL/REPORT. Intact exited0; all eleven mutations exited1. Every fixture snapshot was unchanged across the verifier call; the actual packet was unchanged. Controls used the same verifier hash and preceded the final metadata/report/seal additions. They are proportionate copied artifact controls, not independent review or controls on a fabricated mathematical claim. Results are `qa/integrity-controls.json`. A separate final actual-root invocation uses the emitted detached anchors; its receipt is outside the sealed payload at `work/final-verification.json`.

The exact public artifact manifest is `packet/MANIFEST.json`; `FINAL.json` binds that manifest and this outside `REPORT.md`. Public payload files are sealed read-only. `DETACHED-ANCHORS.json` contains the handoff hashes, also emitted in the final response; reading hashes from the same untrusted directory is not a substitute for the externally supplied values. A separate private evidence inventory is hash-bound by FINAL for local provenance, but private bodies/caches are deliberately not members of the public manifest. The read-only public verifier does not audit that private inventory or execute mathematical support.

Verification command, with the literal values from the detached handoff:

```sh
python3 -B packet/public/verify.py . \
  --final-sha256 FINAL_SHA256 \
  --manifest-sha256 MANIFEST_SHA256 \
  --report-sha256 OUTSIDE_REPORT_SHA256
```

The final actual-root receipt is intentionally outside the seal to avoid a circular self-hash. Rebuilds or regenerated QA belong in a new writable copy; they invalidate the exact public artifact set if performed in the sealed draft.

## Outstanding integration and decision boundaries

Formal support is **pending**. According to the user brief only, a separate task concerns deterministic Proposition B rational-mixture/two-bracket algebra with Lean4.34.1/mathlibd13f23b723b8a846827a245b89c10fc7d3f11612, including exact moment, positivity, normalization, strict and boundary assumptions. Its active root was not entered, read or polled. No declaration names, compiled artifacts, independent formal verdict or formal PASS are invented. No full theorem is formalized. The symbolic Python check does not fill that formal gap.

`packet/public/HANDOFF.md` asks the parent to receive and independently review completed formal support, then integrate its actual hashes and precisely mapped coverage in a later immutable draft. Independent manuscript review and all later acceptance/count/release decisions remain external. The mathematical draft, bibliography, ten-pattern appendix, exact supporting bytes, clean PDF, inspected page renders, reproducible build scripts, provenance/rights records and implementation evidence are handed off now without waiting for the concurrent formal work. No publication or acceptance follows from this handoff.
