# Independent focused manuscript revision audit, round 2

**Verdict: PASS_REVISION. Required fixes: none.** One optional documentation cleanup is separated below.

This is the manuscript/revision-readiness gate for the frozen full-scope r2 package. It does not award acceptance, change the campaign count, certify priority, or establish a full Lean certificate. The earlier mathematical proof PASS remains historical evidence; this audit does not issue a new independent full-proof verdict. Nothing has been narrowed.

Author: Myeongjin Kang, no affiliation. Review performed as the explicitly T3-owned GPT-6.1-Sol/high child at standard speed, without nested agents. Original review prose is CC BY 4.0; original review code is MIT; third-party rights remain with their sources.

## Authentication and scope preservation

I authenticated the exact r2 `output-manifest.json` bytes **before parsing** them: 9,756 bytes, SHA-256 `ffb8d4f9b4e634375b59c4b73db503c8d1a46a5ecb4862601cd728f4b7606027`. Every one of its 59 payload records matches its byte size and SHA-256; the complete handoff has exactly 61 files including that manifest and `SHA256SUMS`, with no symlinks. All 55 referenced repository inputs match. The supplied additional pins also match:

- `main.pdf`: 162,394 bytes, `7108d83f47b34fe7668d096bfcc90cbacd538e2f34984a742e824f139bc45b33`.
- `public-manifest.json`: 6,451 bytes, `69a130a3e5d199277c2c7105b4e51c7a0fba972d7614aab86cc30236f515ac53`.
- `support/verify_package.py`: 5,885 bytes, `3acff8ff4a3312245286c429e2ee00e2eb2c864877d3d160b85e4adf0e6f746a`.
- Full prior manuscript audit: 20,041 bytes, `caf0e282fa79dce82acdd12f8e188f1ab9f736d5a9024e729829bf63900f3df8`.
- Public ZIP: 251,986 bytes, `587a23f4552ad14a7735bf7e23e2d98ac6d143cf26470a92c06af805d290ace6`.

I read the complete prior manuscript audit and parent `manuscript-review-r1-disposition.md`, the r2 README, source map, responses, formal scope, metadata, revision record, rights and code provenance, as well as the complete revised verifier, freeze script, parent regression script and parent r2 result records. Parent checks were treated as evidence to inspect, not as this independent review's tests.

Independent raw-byte comparisons against frozen `kn-minus-edge-manuscript/main.tex` establish:

- Theorem A's environment: 591 bytes, SHA-256 `248a8177e376bf948cc90c6d8b0ca1f81e7f91d8b8822a5fefc33f57d0aeed26`, identical.
- Corollary B's environment: 360 bytes, SHA-256 `ed104baed538a64f45a56c63f985f8f973896e5a8496b111809ce66f0f628d3e`, identical.
- Complete Sections 2–6, from the Section 2 heading up to the Section 7 heading: 30,985 bytes, SHA-256 `b799b46b12699885711978611f62b32a49f550df336dc3edfa80c9d8b5776f21`, identical.

Theorem A therefore retains **every integer n>=2 and every edge e**, for ordinary drawings, with `cr(K_n-e)=Z(n)-C(floor((n-1)/2),2)` and the stated equivalent floor product. Corollary B retains **every m>=4 and n>=1**, with P_n a path of **n edges**, and its full floor formula. The distinct novelty boundary is an attribution boundary, not a restriction on either statement.

`receipts/input-audit.json` records these comparisons and independently matches all 271 files in the parent's pre-revision protection inventory. `receipts/main-tex.diff` retains the complete source diff. The final `receipts/unchanged-inputs.json` rechecks this audit's fixed input inventory after all testing and rendering.

## R1: product attribution — resolved

The abstract (`main.tex:61`, PDF p.1), introduction (`main.tex:112`, p.2), Section 7 limits (`main.tex:497`, p.13), README paragraph 5, metadata scope and source-map novelty row now consistently qualify the new minus-edge lower-bound input by **odd m>=13 and n>=2**. The abstract and introduction point to the bounded literature comparison. Section 7 extends its bounded-search statement to the matching product lower bound and expressly denies a priority certificate.

The introduction explicitly explains `n=1`: in OWH Corollary 5.1 the coefficient `n-1` is zero, so the value is `2Z(m+1)` using Harary–Hill. It also credits the matching upper bound to the classical minus-edge upper bound, product identity and Harary–Hill. The unchanged corollary proof on p.12 retains the dropout. The README and metadata agree. No residual unconditional statement that the whole product consequence is new exactly at odd m>=13 survives in the revised public descriptions.

I independently wrote and ran `checks/check_attribution_algebra.py`, without importing any author or parent checker. Exact integer/Fraction checks cover 1,003 complete-graph orders (including very large integers), 301 product base orders at five path lengths, the `n=1` reduction, sensitivity of the OWH expression to its minus-edge input, and 499 odd-order counting deficits. The coefficient sensitivity is exactly `n-1`. The first boundary example is 630 at `(m,n)=(13,1)` and 1050 at `(13,2)`; replacing 420 by the weaker 419 gives 1049 only in the latter case. These are finite arithmetic checks, not a new all-order proof or literature search.

## R2: formal coverage — resolved

Section 9 (PDF p.14), `formal-scope.json`, README, responses and metadata report **PASS_SCOPED_SUPPORT**, not a crossing-theorem certificate. The formal review hash matches `bbb0344dda8194ef776a8c4bc68a8d44894e6cee178fe019a78cfd962f4d3773`. I read that complete review, the full coverage matrix and parent formal disposition. An independent declaration scan of the actual frozen sources gives **47 support theorems, 17 definitions, 9 author control theorems and 16 independent control theorems**. The simp-attributed theorem is included in the count.

The documented support is substantive and correctly scoped: finite tensor-kernel decomposition, first-slot kernel dimension, weighted diagonal nondegeneracy, actual mixed-test degree/missing identities, the twisted rectangular detector, local-test budgets, Lagrange isolation, the root count and generic cancellation/descent. I inspected the relevant actual conditional types: `mixed_dimension_bound` requires both injections, `twisted_detector_from_U4` takes `hU4` as a theorem argument, `localized_twisted_vanishing` retains `hidentify` and `htests`, and `degree_descent` retains the factorization/preservation obligation `hdivide`. These obligations are not supplied by the bare counts.

The r2 paper and formal scope explicitly leave drawing topology/cycles and barycentric boundaries, drawing sums and global/local complete-star identifications, concrete diagonal substitution and four-prime divisibility, descent instantiated on the actual kernel, both evaluation injections and slot swap, orientation factor four and crossing-count comparison, the even responsibility proof, upper drawing, all-order assembly and product corollary paper-only. The underlying formal audit also discloses the uninstantiated bounded-polynomial tensor/symmetric-basis identifications. Generic support is not represented as the completed graph bridge. U4 is neither a new axiom nor an upstream theorem newly proved in Lean here.

No Lean compilation was run for this revision audit. The authenticated separate audit and parent replay remain exactly that historical compiler evidence. Metadata retains `formal_proof_available: false` alongside `formal_support_available: true`; the surrounding scope makes the distinction clear.

## R3: standalone public verifier — resolved

I inspected all 152 lines of the revised verifier before executing it. Public mode reads and optionally authenticates `public-manifest.json`, checks sizes/hashes, safe unique paths, agreement with the allowlist and exact **file** membership, then returns before the ZIP, private output manifest or checksum-file code. Missing files fail through controlled validation. Full mode retains ZIP-member checks, the output inventory, `SHA256SUMS`, and optional referenced-input checks. Authentication of an externally supplied manifest digest precedes JSON parsing.

My independently written `checks/check_verifier.py` ran **43 scenarios** in disposable copies under this review's `work/`, preserving every complete subprocess stdout/stderr in `receipts/verifier-cases.json`. All expected outcomes passed: six successful cases and 37 controlled exit-1 failures, with no traceback or unexpected stderr. This was a separate implementation and execution, not a rerun of the parent's 20-case script.

The clean ZIP extraction contains exactly **40 members: 39 allowlisted payload files plus the public manifest**. It contains no ZIP, private output manifest or `SHA256SUMS`. Both unanchored public verification and externally anchored public verification from an unrelated working directory succeed. The full frozen handoff also succeeds, including its 55 referenced inputs.

Adversarial cases include missing nested code and PDF, altered PDF, a file replaced by a directory, extra nested file, missing/invalid/malformed manifest, authentication before parsing, duplicate keys/entries, incorrect JSON types, noncanonical/traversal/absolute/Windows paths, invalid byte sizes and digest syntax, payload and ancestor symlinks, a dangling symlink, FIFO, altered/extra/invalid ZIP data, absent handoff records, and corrupt/duplicate checksums. Each intended rejection produces `VERIFY FAILED` with exit 1.

Two positive semantic controls prevent overclaiming: an extra empty directory is allowed because the contract concerns file membership; and self-consistently altered payload/manifest bytes pass without an external anchor, then fail with the original anchor. The README already explains consistency versus origin and instructs checking both verifier and manifest hashes externally. These are correct limits, not remaining defects.

The actual allowlist and ZIP contain no third-party paper, publisher/web/survey extraction, pinned upstream source or internal review text. Full-manifest authentication, ZIP contents and copied extracted bytes agree.

## Historical evidence and PDF inspection

The source map explicitly labels reading extents as inherited r1 records unless marked r2; its closing paragraph identifies the r2 parent's narrower reading. It preserves unavailable-source limits, including no direct reading of Zheng, instead of claiming a fresh primary-source audit. `revision-record.json`, the README and support provenance identify the computational receipts as unchanged r1 evidence. The table now says the long modular subset was re-executed for the original package. The relevant mathematical scripts and all eight retained mathematical receipt/output files are byte-identical to r1. I did not rerun R1–R9, the inherited checkers or the 20-minute mod-p subset to manufacture new activity.

I independently rendered the authenticated PDF at 120 dpi, inspected **all 15 individual page images** and three overview sheets, and checked the extracted page sequence and every numbered footer 1–15. The revised attribution, formal-status and table text, full formulas, bibliography, tables and degree display fit; no clipping, overlap, lost page or broken reference was observed. The title and PDF metadata identify Myeongjin Kang without an affiliation. All outer 0.3-inch borders are clear. `qa/visual-review.json` records per-page evidence.

The actual authenticated r2 build log has zero overfull boxes, zero undefined references/citations and zero rerun warnings. Three inherited underfull boxes remain in source-pointer prose. The five trailing-space diagnostics occur only in the retained raw `checks/build/main.log`, not authored sources. No TeX rebuild is claimed here; this is an independent inspection of the final PDF and existing exact build provenance.

## Optional issue, not a gate objection

**O1, low severity — `RIGHTS.md:9`.** Its inherited sentence says the survey extraction `work/chn-v5.txt` is present in this directory. The r2 README correctly says that scratch was omitted, and inspection confirms its absence. A future documentation cleanup can identify the location as historical r1 scratch or remove the exception. The public boundary is already correct and no third-party bytes leaked, so this does not block PASS_REVISION.

## Deliverables and limits

`input-manifest.json` inventories exact input sizes/hashes, distinguishing fresh reading from byte authentication and reused evidence. Eight live orchestration-context records retain their initially observed hashes separately from the fixed mathematical/manuscript inputs; the final unchanged-input receipt reports any context changes without rebaselining their initial hashes. `output-manifest.json` inventories every review output except itself and `SHA256SUMS`; the latter also covers the output manifest. Their externally reported hashes accompany this review's delivery. `checkpoint.md` was saved before the independent tests and final packaging; this substantive review was saved before final sealing. `provenance.json` and `README.md` state the reproduction commands and limits. Corrected reviewer-harness assumptions, including initially treating live orchestration metadata as frozen, are preserved in `receipts/harness-development.txt`; they were not author defects.

All writes stayed in this assigned review directory, including disposable extraction/control copies. No author byte, shared index or campaign ledger was edited. No agents were spawned. Nothing was staged, committed, published, submitted, accepted or counted. No fresh priority search, source-truth audit, full mathematical re-review, Lean build, long modular run or TeX build is claimed. This PASS_REVISION addresses manuscript/revision readiness only.
