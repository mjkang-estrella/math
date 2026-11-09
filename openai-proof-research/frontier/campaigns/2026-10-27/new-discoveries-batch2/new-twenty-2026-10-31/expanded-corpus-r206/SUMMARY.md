# Reservation r206: bounded investigation, no qualifying candidate

This lane has exactly 20 ID-keyed dispositions in `results.json`. There is no new rigorous resolution and no Lean endpoint to submit. Discovery credit is zero. Seven records are excluded from a discovery route; thirteen are parked with explicit gaps. Parked does not mean open in the literature or novelty-cleared.

The strongest sustained routes were 336857 (meandric partners), 331712 (exponential domination in generated subcubic trees), and 324797 (4-matching covers). Additional exact baselines addressed 326579, 329098 and 331531. No counterexample survived because none was found. Consequently there is no strong-lead Lean packet; `CANDIDATE.md` records this explicitly rather than supplying a surrogate theorem.

## Completed computations

| MathDB ID | Completed scope | Outcome |
| --- | --- | --- |
| 336857 | Every unordered pair of noncrossing partitions through n=12. At n=12: 208,012 partitions and 21,634,392,066 pairs. | Maximum 12,198, with 12 maximizers including rainbow. Through n=9 the actual Kreweras orbit equals the maximizing set; n=10..12 checks count and rainbow membership, with orbit interpretation using source symmetry. |
| 331712 | All operation-generated unlabelled tree types at orders 1,4,7,10,13,16,19: 1,1,2,7,25,128,655. Every subset smaller than the conjectured domination number tested with blocked-distance weights. | No smaller dominating set. Independent Python and C implementations agree through16. The order22 run was CPU-killed; **no completed coverage at22**. |
| 324797 | 500 reproducible seeded labelled graph samples, orders8..12 and sizes n..min(22,2n). All 4-matchings generated and exact cover decisions made for coverable samples. | 350 samples were4-coverable:321 attain the base chromatic/edge-count bound;29 require a larger cover, in every case explained by the conjectured splitting terms. No formula counterexample. Samples include disconnected graphs, so the admissible connected sample count is smaller than500. This is not exhaustive graph enumeration. |
| 326579 | Entire binary three-register instruction Cayley graph, all40,320 permutations. Both block splits, 96 independent products. | Additivity holds on every checked product. |
| 329098 | All zero-sum-free sorted multisets over C6^2, 2,111,759 recursion states. | Maximum cross number14/6;216 extremizers, none containing order6 elements. The minimal-zero-sum clause was not checked. |
| 331531 | Symplectic W(3,2), rank2,t1;32,768 subsets of15 generators. | Maximum3,15 maximizers, all point-stars. Known small-rank baseline only. |

These are numerical diagnostics, not formal proofs. No source-reported verified range was found for the meandric conjecture, so this lane does not claim to have exceeded the authors' range. Each process has its full log in `logs/`; numerical scripts are in `scripts/` and small structured results in `outputs/`.

## Source-based dispositions

- **324835:** source withdrawn in arXiv v3 on2018-01-01; old assertion not pursued.
- **329313:** published counterexample in Gonzalez-Sarabia et al., arXiv1707.03285v4, Example6.1. Actual body gives degree4 distance1 against predicted2 on the F4 nested Cartesian set. Zero credit.
- **330366 and330367:** intended down/up-set directed-path claims already proved by Pinto in the assigned source. Arbitrary disjoint sets in the vertex MathDB paraphrase are not a new conjecture; no paraphrase-only refutation claimed.
- **336935:** Conjecture4.8 at p3 gives r, contradicting its own Theorem4.2 value r+1. The projective-plane Hamiltonian case also conflicts with Theorem4.5. This is an excluded source-internal formula correction, not a new mathematical discovery. Typeset conjecture body remains unverified.
- **372263:** Rizzoli-Thomas2026 refutation, acknowledged in source v3, with a prior formalized general family in Lean Pool. Zero credit.
- **397830:** the exact claimed ionization bound is already Theorem1 in the assigned2012 report, citing Dall'Acqua-Solovej2010. Zero credit.

Partial prior resolution: Aksu-Green prove the ghost upper bound and most lower-bound cases (324888); extraspecial odd-p exceptions require further work. Polcyn-Rucinski's Theorem7 and conditional identity settle the eventual path clause of330699; the triangle clause was not fully cleared in this lane. No finite small-n test can refute a claim allowing unspecified small exceptions.

Deep or semantic gaps remain for334673,337765,370460,372195 and398468. The KL public-submission lead is not adopted as an exact-Q proof. The fighting-fish five-statistic enumeration needs a faithful independent model. The Ban-Linial item has explicit inherited family-overlap risk. The prime-valence lattice problem requires an infinite structural argument.

## Provenance and prior-art limits

`raw/` preserves each exact corpus line including newline. `extracted.json` binds one-based chunk line, chunk SHA256, raw-line SHA256 and UTF8-statement SHA256. Historical notes and both ledgers were read without modification; bounded historical grep hits are retained in `history-matches.txt`. Inherited family snapshots and hashes are in `outputs/inherited-family-read.json`.

All listed source arXiv versions were requested, retained, and text-extracted when a PDF existed; v3 of the withdrawn superposition paper has no PDF. Review depth varies by record and is stated explicitly. This is not a claim to have read every proof in every version. Publisher bodies are not all compared: some landing pages were accessible, Oxford returned403, and the two Rucinski institutional PDF routes returned HTML homepages rather than papers. Those responses are preserved and not treated as evidence of paper contents. One exploratory heterochromatic DOI was wrong and returned404; the correct DOI is10.1016/j.disc.2018.06.030. No conclusion relies on the exploratory DOI.

Live registry heads from `/commits/HEAD`:

- Lean Pool: `01db1d7049cf9668bda1e9e106875ee1278b43e6`.
- Omega: `21d479540aeed5fa1e5bcbf4767e3772181cf8f2`.
- OpenAI/math: `4eaee87548250b2682affda7d05d947c05554bae`.

Lean Pool `LeanPool/projects.yml` and all listed candidate files were fetched at the pinned head. Eight spaced unauthenticated repository queries returned zero results; these limited repository searches do not clear all public code. Truncated root trees were replaced for relevant negative screens by complete Omega D5(14,057 entries), Omega Problems(1,757), and OpenAI preprints(13,578) subtrees. Registry path screens are not exhaustive proof-body audits. Lean Pool's actual Saxl catalogue entry establishes a relevant public formalization lead; the similarly named OpenAI Saxl comparator is a different representation-theoretic conjecture.

All direct HTTP responses have immutable URL/time/status/hash receipts indexed in `outputs/http-receipts-index.json`; web-tool search output snapshots are in `outputs/web-search-*.json` (the first search is retained in the conversation transcript). Denied routes were not retried, TLS verification stayed enabled, and no access denial was treated as novelty clearance. Search results and accessible primary bodies do not cover all citing literature, theses, technical reports or publisher corrections.

## Resource and handoff notes

Numerical runs used `scripts/limited.py`: affinity at most2 CPUs, inherited per-process CPU120s, wall140s, sampled aggregate process-group RSS6GiB, `MALLOC_ARENA_MAX=2`, lane-local temporary directory. The watchdog is sampled, not a cgroup/transient-peak guarantee. The order22 tree run ended with signal9 at approximately120 CPU seconds and was not restarted. The n12 meander run completed in112.6 wall seconds. No Lean command or leanchecker was run, and no dependency rebuild is claimed. No numerical or network job remains at handoff.

No git commands, shared ledger edits, child agents, browser tabs, uploads, external messages or author contacts were used. All created artifacts are in this lane. Full acceptance, independent review, a literal Lean endpoint and novelty clearance remain absent; none of the bounded confirmations is proposed for campaign credit.
