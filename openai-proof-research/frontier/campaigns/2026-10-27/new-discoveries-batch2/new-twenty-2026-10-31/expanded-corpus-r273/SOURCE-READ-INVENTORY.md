# Source and history inventory, actual limits

Work performed on 2026-11-05 UTC in r273, Sol 6.1 high/default discovery and ordinary proof only. Ancestor project, batch and campaign AGENTS and the full TASK.txt were read. Current STATUS says 52/60 beyond 39 prior; historical batch ledger still says 9/30 and is not substituted for current STATUS. Upstream pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and catalogue routing instructions read. Selected catalogue content, ledgers and previous family notes were inspected; not every old manuscript or every ledger entry was reread.

## Literal records

All 20 full parsed records and their literal statements were read. raw/ID.jsonl preserves the original complete normalized-corpus line, including newline. raw/ID.json preserves the parsed record; results.json includes it too. provenance.json gives absolute corpus chunk path, one-based line, complete chunk SHA256, exact raw-line SHA256 and UTF-8 statement SHA256. The corpus is the cached probxiv retrieval, not a newly verified current MathDB crawl. Empty solutions and open labels have no novelty force.

## Primary retrieval versus reading

fetch_sources.py fetched current abs and PDF for the 19 arXiv records and the EMS page for 396224. All 19 PDFs converted successfully; 396224 has no primary proof body read. fetch_more.py archived older advertised PDF versions (the final listed version uses the unversioned main PDF), plus the classification companion, Pankov successor, registry and author pages. Each receipt contains URL, UTC, status/error, bytes and SHA where a response exists. version-inventory.json stores submission-history excerpts and advertised versions. Parsing a history is not a proof read.

Actual selected primary reading for each ID is explicitly recorded in results.json. For the main 378416 route: sole advertised math/0405279v1, Definitions 2.1–2.5, Theorem 2.2 and duality Theorem 2.6 proof, relevant simplex/cross-polytope examples and Conjecture 4.9 with partition classification context, were read. The classification companion math/0310165 Definition 1.1, Definition 1.2 and selected Section 2 uniqueness proof explain actual codimension-two link convention and K(P). Pankov 1509.03754v3 Section 2.1 joins and Section 3 ordered-facet vertex shift/least period passages were read. Its full Coxeter and z-connectedness proof corpus was not audited. This is NOT all-body clearance.

For 377311, the post-Conjecture 3.8 pair is source-known. Selected First Stabilization Theorem proof uses independent repeated blocks to make generic trial sources contractible. For 380007, Section 5 interior-offset construction, Theorem 5.1, Conjecture 5.5, examples and PC4 diagram description were read. These gave substantive obstructions beyond an initial failed shortcut; ATTEMPTS.md records them.

For 377813, source's affirmative-answer sentence is supported by inspected Theorem A/Corollary B.1 recursion statements and selected proof passage. This is sufficient to reject novelty; not a claim of a full 48-page proof audit. For 376609 the Lemma 5 proof was read, and the complete classical general bound is proved in ATTEMPTS.md. For 377031 the count definition, scaling passage and Conjecture 2 were read. No known full theorem is called novel.

## Journal, citation, version and figure limits

The author publication page identifies the printed zigzag source as Southeast Asian Bulletin of Mathematics 29 (2005), 301–320 and links a journal PDF. That exact author-listed URL returned HTTP403. It was not retried, rehosted through a proxy, or accessed with TLS disabled. No statement of journal-body clearance. Deza's author site produced certificate validation errors on the publication page and 2010 survey PDF; no validation bypass. The independently accessible author's newer publication list was fetched successfully. Pankov's Springer 2017 HTML was fetched, but only the corresponding selected primary PDF passages were read. All its versions and all its citing bodies were not read. The EMS Engel journal PDF was independently fetched successfully and selected target/exception passage compared; no global Engel resolution claim.

Main source figures 1–3 concern other map families, not a printed rank-nine (3,6) object. Text-extracted examples, formulas, table descriptions and partition scope were compared. No full visual inspection of every figure/table in every source was done. In particular the bivincular pattern diagram for 319971 and its volume-partition definition remain unresolved, not silently reconstructed. For 376617 the printed q=4 sum/modified-components construction was read in prose; a new perturbation is not offered as a distinct discovery. No witness eligibility is inferred merely from degree, dimension or nonisomorphism.

Full target-version passage comparisons were selective: cached older files exist for 319398 v1/v2, 320253 v1, 320402 v1/v2/v3, 323069 v1, 326770 v1, 377031 v1, 377813 v1 and 381095 v1. Where outputs were truncated only the visible selected passages are counted as read. No assertion of every-version full-proof or latest-corrections completion for all 20. Extra referenced papers for Bressoud and broken-diamond thresholds were not fully fetched/read. These limits block novelty clearance and are preserved in every result entry.

## Historical coverage

history-matches.txt is a bounded entire-batch Markdown and results/rejection JSON screen for exact ID word boundaries, all 19 arXiv IDs and selected family terms. historical-paths.txt came from an earlier unbounded-numeric preliminary search; numerical substring hits there can be false positives and were not treated as technical history. Specific notes actually inspected:

- hereditary-trace-fresh-r1/BORG-ASSESSMENT.md: 321318 same source as 321319; modern 2026 hereditary results recorded there and the exact remaining cross-sum bridge. These newer bodies were not re-reviewed here.
- r265/378417 Lins triality disposition and r720/378414 product-of-polygons disposition: same source as 378416, different parked questions, no acceptance precedent. No held target's solution reused.
- Earlier Woodroofe source-family scouts: largest-link preservation obstruction; strict and t-intersection variations remain same family.
- r263 unfriendly-partition alias; r264 Whitehead/polygonality family; r269 related Engel family; r232 same q-series source but a different conjecture. Exact outcomes are not inferred from filename matches alone.

No global claim that unassigned IDs were never investigated. Gaussian316253 root exclusion, Delta377613 park, path-spectrum and polar root exclusions all respected; no attempt to redeclare them eligible.

## Current public registries

On 2026-11-05, independently lawful GitHub history page /openai/math/commits/main returned 200; its first displayed commit was 4eaee87548250b2682affda7d05d947c05554bae. Public raw main CONTENTS.md returned 200 and was term-screened for zigzag/Petrie, resonance, q-series, Ulam and related family terms. Generic Ulam stability entries were unrelated. No target-matched theorem body was identified/read; catalogue absence does not clear all sources. No current complete tree is claimed. No GitHub API request or denied API reroute was made.

A guessed community projects path returned 404. The correct LeanPool path was taken from the existing r272 receipt: public raw Vilin97/lean-pool/HEAD/LeanPool/projects.yml and README.md both returned 200. A bounded term screen found only unrelated Poincare-resonance entries; no zigzag/Petrie target. HEAD was not independently pinned for LeanPool, and no exhaustive candidate-repository or theorem-body audit was done. This is routing evidence, not priority certification. Earlier complete subtree/catalogue caches were not represented as current full registries.

Public search additionally routed the Mondello affirmative resolution, author partial-Hadamard maximality slide, Pankov successor, later Artin Property-H classes, unrelated similarly named Bressoud identities, and the bipartite energy companion. Search dates/crawl labels are not publication chronology proofs. Except for the explicitly fetched and read bodies above, search results were not promoted to proof-body review. No exhaustive citation census was completed. No account, browser tab, contact, upload or publication action was taken.

## Execution bounds and reproducibility

Three finite HTTP/text jobs use archived scripts fetch_sources.py, fetch_more.py and fetch_qualification.py, each run with python -I -B and timeout 140, ThreadPoolExecutor(max_workers=2), CPU limit120, address-space6GiB. Every request and text-conversion result is logged in fetch*.log and per-request receipts. All three execution sessions returned exit0 and were closed before delivery. There were no solver/Lean/numerical searches or heavy enumeration jobs. Early extraction/inspection used inline Python before archived build/verification scripts; this inventory is not a claim that every exploratory shell command was archived as a standalone script. No peak-RSS measurement was collected; 6GiB is the imposed address-space cap, not an observed RSS statistic. build_delivery.py and verify_delivery.py run under -I -B with the same CPU/address-space bounds. Final verification rereads literal corpus lines, checks exact key set, rehashes reservation and writes the manifest. No shared files were edited.
