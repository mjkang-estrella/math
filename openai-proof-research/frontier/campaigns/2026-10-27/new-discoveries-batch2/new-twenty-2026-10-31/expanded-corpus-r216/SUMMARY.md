# Expanded corpus r216 research report

**Outcome: zero qualifying new solutions; 20 ID-keyed dispositions delivered.** No acceptance claim, ledger change, or Lean certificate is made. Six routes were excluded from discovery investment; fourteen remain parked with explicit gaps. This is a bounded investigation, not a completed novelty clearance or a solution of the reservation.

## Findings

- **359187:** an exact public Lean proof already exists in Omega, introduced 2026-10-02. Actual target and proof body were read, including its literal orbit definitions and coboundary argument. See `CANDIDATE.md` and `outputs/registry-screen.json`.
- **353969:** the current primary paper itself refutes the Kühn–Osthus statement in Proposition 1.6. The proof and degree comparison were checked.
- **366279:** the unqualified wreath-product statement is contradicted by exceptions explicitly printed in its source and companion paper. They are not discoveries.
- **398198:** the standard intended packing/covering conjecture has a pinned prior OpenAI refutation. The corpus reverses restriction/contraction conventions, so the known theorem is not silently asserted to refute that reversed literal wording.
- **323690:** the source itself has a three-variable equation beneath a four-variable heading. A tiny avoiding-colouring diagnostic is a zero-credit formulation route.
- **327907:** the classical `(37,9,2)` biplane plus a short union bound contradicts the equality. This is retained as a rejected routine bridge, with a complete ordinary argument and an independently checked incidence structure in `CANDIDATE.md`.

The revised Kempe conjecture, **357770**, is distinguished from the already refuted original conjecture. Its strict inequality excludes using the source's equality construction as a counterexample. The dense-hypergraph certificate conjecture **325888** is genuinely stated in the primary source despite inconsistent corpus status text.

## Exact computations

All executed numerical searches used `scripts/run.py`: CPU 120 seconds, wall 140 seconds, address space at most 6 GiB (therefore RSS bounded above by that), affinity at most two CPUs, `MALLOC_ARENA_MAX=2`, lane-local temporary directory, isolated Python with bytecode disabled. Runs were sequential. Logs and resource receipts are in `logs/`.

| Route | Completed coverage | Result |
| --- | --- | --- |
| Young graphs 328933 | Every `2<=n<=56`, `3<=t<=20`; 990 pairs, max completed base 60,761 | No failure; CPU cap during n=57 |
| Rowmotion 359187 | `[6]×[7]`: 477,097 states, 3,497 orbits; `[5]×[8]`: 283,243 states, 2,849 orbits; `[4]×[9]`: 97,861 states, 1,741 orbits; `[3]×[10]`: 18,811 states, 661 orbits; `[7]×[7]`: 1,784,114 states, 9,758 orbits | All orbit sums zero; subsequently excluded by exact public Lean proof |
| Rowmotion interrupted run | Generated 5,953,639 convex sets on `[7]×[8]` | Stopped when public proof found; no complete orbit-coverage claim |
| Max-Welter 323048 | All 61 one-coin, 1,830 two-coin, 35,990 three-coin and 521,855 four-coin positions on squares 0..60 | Exact mex data; finite mismatches cannot refute ultimate periodicity |
| Frankl 326319 | All 65,535 nonempty labelled edge subsets of a 4-by-4 bipartition | All passed; diagnostic, overlapping known cases |
| Biplane controls | Classical cyclic designs `(7,4,2)` and `(11,5,2)` | Exact domination numbers 4 and 5; no new theorem |
| Biplane obstruction diagnostic | Classical cyclic `(37,9,2)` | Full incidence validation and union-bound exclusion of domination size 9 |

The Young graph generator was independently compared against direct two-digit equation enumeration for all 171 pairs `3<=g<=20, 2<=k<g`. Convex-set generation was independently checked against all subsets on `[2]×[2]`, `[2]×[3]`, `[3]×[3]`. These validate diagnostics, not formal theorem semantics. A C++ implementation was written but never compiled because this environment has no C++ compiler; it is not evidence.

## Provenance and source review

`raw/` retains each exact corpus JSONL line including its newline. `provenance-enriched.json` records one-based line numbers, seven source-chunk hashes, raw-line hashes and UTF-8 literal-statement hashes. `results.json` has exactly the 20 reserved ID keys and includes literal statements, source receipts, actual review sections, computations and missing lemmas.

All 20 primary source landing pages were obtained. The 19 arXiv primary papers were obtained as PDFs and text; the remaining primary source is the EMS report landing page, whose full original report body was not recovered. The investigation read target statements and selected adjacent proof bodies, not every proof of every paper. All three versions of Kendrick's arXiv source, its journal PDF, both versions of the initial rowmotion paper, the 2025 rowmotion follow-up and selected companion papers were acquired. Not every historical version of every parked paper was read. `logs/example-figure-inventory.json` is a printed-mention inventory for the selected sources and versions, not an exhaustive mathematical classification of their constructions.

Live literature and citing-work searches are preserved in nine `receipts/web-*.json` files. They included 2026-scoped searches and institutional/thesis leads. They are bounded non-findings where no hit was obtained, not evidence of global novelty. No Crossref, Semantic Scholar, arXiv search API, ScienceDirect or DBLP page was deliberately fetched. Search-engine results may mention these hosts; no denied URL was followed from them.

The live registry screen fetched HEADs for Lean Pool, Omega and OpenAI/math. It screened the complete Lean Pool path tree, projects metadata and all ten candidate files, and the complete Omega D5 and Problems trees. Five GitHub repository searches returned zero repositories. The OpenAI full recursive HEAD tree is truncated; the inherited complete pinned preprints listing was also consulted. No claim of complete public proof-content coverage is made.

The required ancestor instructions, campaign ledger and inherited accepted/excluded rules were consulted. An ID-pattern search over historical campaign SUMMARY/CANDIDATE/results files found only incidental number/hash matches; no actual prior reserved-ID disposition was found within that bounded scope. This is not a corpus-wide guarantee.

## Limitations and process defects

The initial finite rowmotion and Young-graph runs began before completion of the full Omega screen. This violated the requested ordering; the rowmotion route was stopped when the public exact proof was found. No novelty claim relies on those runs.

An early HTTP filename allocator had a concurrency race: the first `1404.6358` abstract receipt/body numbered 6 was overwritten by the later OpenAI tree response using the same number. The surviving receipt 6 correctly describes the OpenAI response; the abstract was reacquired under immutable receipt 54. The lost initial abstract receipt is not claimed preserved. The allocator was changed to reserve unique filenames before requests; no other observed collision was found. Downloads and all output remained inside this lane.

The pass did not execute meaningful finite searches for every remaining finite-object conjecture, and it did not satisfy the requested several-hour sustained depth across two or three still-eligible mechanisms. In particular, source-faithful alternating-circuit, fractional-extension, Kempe, code-automorphism and genus-criticality searches remain unperformed. Their gaps are explicit in `results.json`. No dummy Lean endpoints were created to conceal these gaps.

No packages were installed, no downloaded code was executed, no child agents or git were used, no other lane or shared ledger was edited, and no background search remains. There is no Lean replay, axiom audit, or new accepted count to report.
