# Expanded corpus r47 — investigator handoff

**Zero accepted credit. Campaign remains 3/20 beyond 39 prior.** No shared ledger, reservation, historical report, dependency, git state or other lane was edited. No child agents, browser tabs, uploads or external messages.

Exactly **40 ID-keyed dispositions** are in `results.json`. All forty literal cached statements were read and preserved as exact raw JSONL lines including newline. Each has one-based chunk line, chunk SHA256, raw-line SHA256 and UTF-8 statement SHA256 in `extracted.json` and `results.json`. This is not forty primary reviews: **six targets** received new primary definitions/selected proof-body review; the other **34 remain literal-only holds**. Body and proof depth is individually qualified, including unread derivations and prior bodies.

## Strongest finding: 353823

`CUT-ORDINARY-PROOF.md` gives a complete ordinary proof of exact Family B Conjecture 2 using the published base-sequence Theorem 3 and even-cut Theorem 19. The new argument assigns binary-place weights 1, 2c, 4c+1, 12c, 24c, ... . For the base game it proves

    1 ≤ n-W(G(n)) ≤ 6c.

Weighted xor subadditivity then forces every partition with xor value G(n) to have at most 6c parts. Every added odd cut above 3x=6c produces more parts, so it cannot hit the old mex; strong induction proves invariance for arbitrary nonempty X,Y, including infinite cut sets.

**This is not a qualified new solution yet.** There is no literal Lean endpoint: formalizing the actual arbitrary-c base-game sequence, or proving its potential bounds directly, is a material unresolved semantic bridge. No surrogate predicate or finite-check theorem was produced. An independent significance review must decide whether the argument is an ineligible routine consequence of the known closed formula. Successor/published comparison is bounded, not complete. DDLP's AP-test Proposition 13 and Omega's Family A body were read; neither directly provides the exact formal Family B endpoint.

## Other sustained routes and exclusions

- **354171:** recovered the Fourier meaning of positive weighted extremal designs. Examined code classification, an adjacency/closed-neighborhood lower bound, and tensor/sum constructions. Exact code diagnostics reproduce known d=7,8,9,11 supports. The universal positive-weight lower bound remains missing; Bonisoli only handles linear codes. No new result.
- **354003:** recovered rational Eisenstein coefficient normalization and both recurrences. Pairing terms proves a mod-two doubling mechanism already overlapping source special cases. General digit-sum content needs a noncancellation lemma, including even denominator issues at k=2 mod4. Source already tested to3500, so no redundant small sweep was offered.
- **353711:** actual Theorem 3.3 and proof already resolve the bound. Excluded as known.
- **354369:** actual Iskander Counterexample 1.8, k=14, partition(2,1), refutes the real-rootedness conjunct. Displayed polynomial and scope read; accompanying full derivation/code not audited. Excluded as known; positivity alone not declared resolved.
- **354173:** Lum's public Theorem 1.5 body claims the exact integer-r threshold, unlike its abstract's ceiling wording. Its proof was read and contains rounding inconsistencies worth review. Withheld due to a prior public full-scope claim; no assertion that this proof has passed independent validation.

All further mathematical attempts and precise missing lemmas are in `OTHER-ROUTES.md` and per-ID results. Related inherited families 332101/354087 (Sudakov), 334037/354260 (circuit cover), and adjacent 353822/353823 (Family A/B) are retained distinctly; no inherited rejection was overturned.

## Sources, registries and limits

`receipts.jsonl` records dates, requested URLs, status or timeout, final URLs and actual received-byte hashes. No hash invented for the timed-out direct author cut PDF; its published rule/conjecture passages were separately read via web extraction. A lawful arXiv copy is retained. No JKU, MathDB or Palomar denied route was retried. `cut-web-search.json` retains the targeted search result. Not all search engine leads were retrieved or read.

OpenAI/math current HEAD at 13:14 UTC is unchanged at **4eaee87548250b2682affda7d05d947c05554bae**. The complete preprint tree **3f56f68a176b4494c346091ea0a319651bc217ec**, 13578 paths, is reused by verified local hash from r10. The truncated root cache is not used as a complete listing. This pass screened relevant paths, not all manuscript bodies.

Omega current HEAD at 13:15 UTC is **e9b39e568e8e0b68788ec0f007bc0107069db513**, changed from the inherited head. The compare API reports two commits and one changed docs file, with no D5 or Problems changes. Thus the inherited complete D5 (13297 entries) and Problems (1629 entries) listings were reused for the scoped path screen. Family A Lean body was fetched at the current pinned revision and read. This is not global proof/history clearance. An initial mistaken teorth/equational_theories probe is explicitly marked unrelated in `registry-review.json`; it supplies no clearance.

All five reservation-bound input hashes match; `input-verification.json` records this. Mutable campaign ledgers were read separately as administrative context, with snapshot hashes in `ledger-context.json`. The reservation establishes absence from specified checked assignment indexes only. Corpus inventory figures remain 95675 distinct historical IDs, 87990 retrieved and 7685 stubs; the old10000 queue is not the entire corpus.

## Reproduction and formal status

Run `extract.py` to reproduce raw/provenance extraction, `diagnostics.py` for finite ordered-composition nim-set and Walsh-code diagnostics, and `finalize.py` to regenerate dispositions/context/environment. Network retrieval scripts retain exact URLs and may observe later content; use retained byte hashes for this run. Full diagnostic output is in `diagnostics.log`; completion output is `finalize.log`. These scripts are diagnostics, not formal certificates.

`environment.json` records actual Lean4.34.1 commit5045d0056413266e57c625dcd7c365b10e377c52 and read-only mathlib manifest pin d13f23b723b8a846827a245b89c10fc7d3f11612. No Lean packet, extracted replay, all-declaration audit or upstream rebuild PASS is claimed. No mathematical local Lean declarations were introduced. Resource-heavy scripts were CPU-affined to two CPUs with explicit memory/CPU/wall budgets; all processes finished. Acceptance and any further independent review belong to root.
