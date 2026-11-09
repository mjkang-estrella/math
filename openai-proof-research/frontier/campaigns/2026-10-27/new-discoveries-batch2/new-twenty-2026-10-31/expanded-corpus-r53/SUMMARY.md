# Expanded corpus r53 — investigator handback

2026-11-01. **Zero proposed credits; no eligible literal Lean endpoint. Campaign count remains4/20 beyond39 prior.** Root alone accepts. No ledgers, historical reports, dependencies or other lanes were edited; no git, agents, browser tabs, external messages, publication or uploads were used.

## Exact scope and provenance

Exactly40 reserved ID-keyed entries are in `results.json`. All40 literal statements were read. Exact raw JSONL lines, including their newline, are preserved individually in `raw/`; each entry binds its original chunk, one-based line, full chunk SHA256, raw-line SHA256 and literal decoded-statement UTF8 SHA256. `intake.py`, `intake.json`, and `statements.txt` reproduce this intake. `verification.json` and `verification.log` record40 keys, raw hashes/newlines, statement hashes and successful-download hashes verified.

This is an expanded-corpus assignment, not the old10000 queue. The accessible inherited inventory has95675 distinct historical IDs,87990 retrieved records and7685 stubs; this pass does not claim to have reviewed the full inventory. Reservation exclusion/absence is administrative assignment evidence, not global technical nonreview or novelty. All five reservation input bindings rehashed identically, including the older ledger binding. The current campaign ledger is mutable context; its hash and selected accepted/held/rejected context are separately recorded in `ledger-context.json`. A stale status string in that ledger does not override the user's4/20 count.

Read applicable project/batch/campaign AGENTS, batch and current ledgers and prior-campaign context. Bounded word-boundary ID and exact-title searches in campaign notes/results/reviews found no inherited ID/title matches. `history-*` and `older-history-*` retain empty results and the relevant search scripts. This excludes neither other file formats nor unindexed technical work; protected and inherited excluded families remain protected. No protected candidate was taken over.

## Actual new review depth

- 40 literal records, **31 literal-only**.
- 9 IDs with newly retrieved primary context;358935 is adjacent/context-only, not a completed target-proof review.
- 8 IDs with selected actual target definitions/theorem/proof bodies read:358937,359147,359148,359262,359653,359711,359719,359721. This does not mean8 entire papers audited.359719's internal Tashkinov lemmas were not all read.
- Three sustained main routes: weighted trapezoid divergence; regular-graph AC/girth; distinct-triangle point sets. Segmentation received additional source-definition/proof review, then was parked for a semantic obstruction. All precise mathematical attempts and remaining lemmas are in `mathematical-attempts.md`.

## Findings

**359721 — routine bridge, zero credit.** Completed an ordinary proof of all upper/lower/sharpness clauses in the literal weighted model. Separate the J-marginal binomial divergence, apply source Theorem53, and retain the conditional entropy and coefficient signs. A two-corner distribution proves the lower bound; compactness upgrades pointwise strictness for d>0 to strictness of the maximum. This is a direct consequence of an explicit published same-paper binomial divergence theorem. Under the campaign's routine-consequence exclusion, no Lean work was started. The complete bridge is reviewable in `mathematical-attempts.md`; this investigator disposition is not independent significance acceptance.

**359147/359148 — unresolved.** Source conjectures, definitions, tables and selected spectral discussion read; distinct author-hosted version retrieved. Completed cubic graph diagnostics at orders6,8,10, with7,552,132930 connected labelings after fixing vertex0's neighborhood. Maxima follow the source trend; eigenvalues are floating diagnostics, not formal certificates. Dense-complement and high-girth spectral-bound routes were also assessed. The missing ingredient is a provable separation against every graph in a competing girth class;359147 additionally needs global optimality. No proof or refutation claimed.

**359653 — unresolved.** The source explicitly counts collinear triples. Hexagon-plus-center gives five classes and fails. Exact squared-distance diagnostics found no at-most-four-class seven-subsets among50388 triangular-disk subsets or11440 square-grid subsets. A diameter/circle-intersection reduction gives only a crude bound18, not7; cross-triangle orbit elimination remains missing. No global theorem follows from these searches. The source's four-triangle conjecture is distinct from its solved three-triangle theorem despite a contradictory metadata references field.

**359262 — semantic obstruction.** Recovered Definitions40/41/43 and read Proposition46's actual proof and Conjecture50. Finite-board outcomes do not certify unbounded outcome segmentation. Exploiting arbitrary region subdivision or an unspecified maximality condition would be a definition correction; no eligible endpoint was promoted.

**Body-supported prior exclusions:**358937 is already refuted in its supplied source, Theorem6.6/Claim6.7;359711 is exactly resolved in the published journal §5.5, whose actual lemma/theorem proofs were read.359719 has a public full-scope algorithm claim in current arXiv v7; exact theorem and algorithm/complexity body were read, but its full45-page internal proof was not audited. Remaining entries are candid holds with individual next lemmas, not assertions of open status or novelty clearance.

## Live prior-art and access limits

Both `/commits/HEAD` requests returned HTTP200 at14:34UTC:

- OpenAI/math `4eaee87548250b2682affda7d05d947c05554bae` unchanged.
- Omega default HEAD `83b70a1d0d6a58bb32521c741805d845d401c5f8` unchanged; nondefault `main` was not used.

Reused the complete OpenAI preprints tree `3f56f68a176b4494c346091ea0a319651bc217ec` by verified byte hash `6ac178a0ebcece8f2c2c9aa1c22022068110bbdae4bb3d1ffa9f1b693b9e0305`. Reused the scoped complete Omega D5/Problems trees from the corrected staller-parent receipt at unchanged HEAD. `registry-screen.json` records exact paths, tree hashes, byte hashes and path-screen hits. Path searches are not all-body or deleted-history clearance. The truncated OpenAI root-tree cache was not treated as complete.

`source-receipts.json` and `extra-source-receipts.json` retain URL, date, HTTP status, actual response SHA256 and bytes for every saved primary/registry response. Primary PDFs and extracted text are local. Web searches supplied leads for journal/author versions; affirmative exclusions rely on read bodies as specified. No universal priority claim, exhaustive specialist search, or live MathDB/Palomar clearance. Inherited403 is not clearance; no denied route was retried or bypassed.

## Environment, resources and reproduction

Actual initial version check succeeded: Lean4.34.1, commit5045d0056413266e57c625dcd7c365b10e377c52. Read-only formal manifest pins mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; actual binary/manifest hashes in `environment.json`. No mathematical Lean module was written, so no sanitized rebuild or axiom audit is claimed. No prebuilt upstream oleans were rebuilt or source-to-olean attested. No dummy endpoint or numerical theorem surrogate supplied.

Run scripts from project root, serially, with CPU affinity0,1 and the wall limits used here:

```
timeout 100s taskset -c 0,1 python <lane>/intake.py
timeout 280s taskset -c 0,1 python <lane>/fetch.py
timeout 160s taskset -c 0,1 python <lane>/checks.py
timeout 90s taskset -c 0,1 python <lane>/diagnostics.py
timeout 90s taskset -c 0,1 /usr/bin/python3 <lane>/graphs.py
timeout 75s taskset -c 0,1 python <lane>/fetch-extra.py
timeout 90s taskset -c 0,1 python <lane>/finalize.py
timeout 70s taskset -c 0,1 python <lane>/verify.py
```

`<lane>` is this directory's project-relative path. Scripts impose2GiB address-space and60–90 CPU-second limits; children inherit CPU affinity. These are address-space/CPU limits, not an aggregate cgroup/RSS claim. Fetches have per-request timeouts, no retry loops. Graph search completed within its budget; outputs retained in `graphs.log` and `graph-diagnostics.json`. Geometry output is retained in `diagnostics.log` and `geometry-diagnostics.json`. The optional graph-atlas tail failed because networkx is absent; graph work was then performed by the self-contained `graphs.py`, without installing anything. Thus `diagnostics.py` intentionally reproduces the retained environment failure after geometry, not a successful atlas run.

`finalize.log` and `finalize-retry.log` retain thread-creation failures of version checking under the restricted child process. The initial unrestricted small version query had already succeeded; finalization records that observed version rather than repeating it. `finalize-success.log` and `verification.log` completed successfully. No expensive or detached background job remains. No acceptance, manuscript, or independent audit requested on this zero-credit packet.
