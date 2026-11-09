# pi-mathdb-primary-qualified-breadth-r343 — SUMMARY

Breadth review of the 50 MathDB records reserved for this lane in
`root-mathdb-core-retirement-r342/reserved-ids.json`, with hypothesis briefs for root to delegate.

## Pre-scientific integrity verification (done BEFORE reading any statement)

- Root manifest `root-mathdb-core-retirement-r342/manifest.json`: 28 payload entries; all SHA256+size
  re-verified against actual bytes; file set exact (excluding manifest.json/verification-receipt.json). PASS.
- Root bindings `root-mathdb-core-retirement-r342/bindings.json`: 23 entries, all originals rehashed and
  matched, including the frozen copies of the r340 queue/coverage/reservation used here. PASS.
- Corpus: `pi-mathdb-full-corpus-inventory-r301/corpus/mathdb-normalized-chunk-0001..0020.jsonl` rehashed
  against the inventory manifest: 20/20 match. PASS.
- Exclusions: `frozen/root-mathdb-accepted-exclusions-r304/accepted-exclusions.json` and
  `historical-dispositions.json` match `root-r304-frozen-sha256.txt`. PASS.

## Reservation-disjointness (verified by direct comparison)

The 50 reserved ids are disjoint from the 333 ids in
`root-mathdb-core-retirement-r342/coverage-delta.json` and from accepted-exclusions and
historical-dispositions. All 50 records are `status=open`, `solution_count=0` in the verified corpus.
The 393907 simultaneous-core retirement (Vandehey 0809.2134 / Fayers 1007.1071 Thm 5.1) was not touched.

## Coverage of the fifty statements

- 50/50 records: full literal statement read from the corpus extract `work/reserved-records.json`
  (73,163 bytes, sha256 ee3283e7eaab654df722e4ae64ab89626575d7c8e199f74be713f4947fb383c8; extract
  contains all 50 full records, one per reserved id). Tags were never used as review.
- Evidence levels: `cached_full_statement_read` for all 50; `primary_body` for 2 (retained PDFs);
  `public_abstract_or_search` for the 12 public resolutions/refutations (abstract/answer-mode text,
  plus retained-body confirmation where stated); `bounded_public_search_2026-10-31` timestamps in
  proposals.json. NO claim of exhaustive current-registry clearance is made.

## Dispositions (dispositions.json, exactly 50)

- 12 REJECT publicly resolved/refuted, each with a named public resolution:
  - 394884 Deza–Frankl 1977 + Cameron–Ku 2003 (statement self-asserts the result).
  - 394888 = verbatim Theorem 4 (incl. "for any vertex u there is an l-cycle containing u") of
    Kelly–Kühn–Osthus arXiv:0806.0933 — retained PDF, body-checked.
  - 394896 = verbatim Theorem 1.1 of Fox–Sudakov arXiv:0707.4159 (same constant 32Δε^{−Δ}) —
    retained PDF, body-checked via pdftotext.
  - 396135 Hayden–Winter arXiv:0807.4753 (all p>1, supersedes p>2).
  - 396220 refuted for k≥171 (JCTB 10.1016/j.jctb.2009.11.003); exact threshold k≤12
    (SoCG 2019, 10.4230/lipics.socg.2019.14).
  - 396805 Hatami–Norine arXiv:1005.2382 (undecidability).
  - 396822 Ellis–Filmus–Friedgut JEMS 2012 (2^{binom(n,2)}/8).
  - 397304 Guth–Katz arXiv:1011.4105 (Ω(s/log s) is stronger than the record's Ω(s/√log s)).
  - 397323 Marcus–Tardos JCTA 2004.
  - 397324 Cibulka–Kynčl arXiv:1104.5007 (settles Raz's question; record statement also has
    `\4` encoding corruption).
  - 398149 arXiv:1209.4270 (statement verbatim).
  - 398218 Hatami–Hladký–Král'–Norine–Peng arXiv:1102.1634 (+ Grzesik independent).
- 11 REJECT famous-hard; 20 REJECT deep; 5 REJECT programmatic (395393 T_{8,8}, 395899/395900
  80-dim lattice, 397266, and none others); 2 REJECT ill-posed/vague (395121, 395627);
  1 REJECT source-gap (397797, corrupted statement); 2 HOLD (395538 medium, 397285 low).
- 2 QUALIFIED candidates → proposals.json.

## Hypothesis briefs (proposals.json, 2 of max 3)

1. **P1 — 396813** `ssat(n,C5) = 11n/8 + O(1)`: exactly Conjecture 4.1 of Füredi–Kim
   (arXiv:1103.0067, retained PDF, body-checked). Open part is the lower bound. Full-scope mechanism:
   connectivity + end-block density lemma + discharging. **Run here (bounded, dual-checked):**
   exact ssat(5)=6, ssat(6)=8, ssat(7)=9 with witnesses; in particular the published bound (6)
   `ssat(n,C5) ≤ ⌈11(n−1)/8⌉` FAILS at n=6 (7 is impossible — exhaustive over all 6-vertex 7-edge
   graphs, two independent definitions agreeing on 23,832 graphs). The hypothesis delegate must
   reconcile this against the published version and push exact values to n=9,10 (planned, not run).
2. **P2 — 396552** finite colorings of Sturmian factors killing monochromatic factorizations.
   **Run here:** on a 10^6-letter Fibonacci word, every color class of the naive family
   c(U)=(first letter, |U| mod k), k=2..6, admits monochromatic boundary paths reaching the end of
   the prefix — the whole naive family is eliminated; any working coloring must be content-sensitive.
   Full-scope plan (both directions), finite interval-exchange reduction and risks in proposals.json.
   Scope objection recorded: fixed-slope results get no full-scope credit.

No third brief: every remaining record failed screening as famous-hard, programmatic, deep, resolved,
vague or source-corrupted; none was promoted on speculative short-proof estimates.

## Retained primaries / provenance

sources/ (all arXiv, lawful public HTTP, retrieved 2026-10-31T04:32:20Z):
- furedi-kim-1103.0067v1-cycle-saturated.pdf — sha256 1f049570ebbe0fbc760c0b6eb964044869bf74184ede791c91f8db78482df4ea
- fox-sudakov-0707.4159v2-density-bipartite.pdf — sha256 c25c69b873dabc5f82bc8da473ae3db92cf9c0ed9cc1617fd6a90b16326348f8
- kelly-kuhn-osthus-0806.0933v2-cycles-oriented.pdf — sha256 23f4d4da67cc020a20de7ba4c4285c75b777489ff914f4964043298fed394569
bindings.json holds 29 flat immutable refs, every one with sha256+size (no existence-only refs, no
corpus duplication, no recursive history trees).

## Bounded computations (all under the fixed guard; peak group RSS ≈ 10–13 MB, well under caps)

- work/ssat_c5_smalln.py / .out — exhaustive n=5,6,7 (guard_exit 0, wall 1.04s).
- work/ssat_c5_crosscheck2.py / .out — dual-definition agreement on 23,832 graphs + n=6 m=7 zero-hit
  under the literal C5-count definition (guard_exit 0, wall 14.2s).
- work/sturmian_mono_factorization_dp.py / .out — Fibonacci word DP, N=10^6 (guard_exit 0, wall 4.1s).

## Failures preserved (actual)

- First Sturmian run was KILLED BY THE GUARD at 210s (exit −9, wall 210.47s): quadratic string-morphism
  generation. Replaced by linear Fibonacci concatenation; the killed run is recorded here, not deleted.
- work/ssat_c5_crosscheck.py (first crosscheck) contained an inverted comparison and an edge-ordering
  bug; found via disagreement on witnesses, fixed in crosscheck2; file kept as the failure record.
- First web-search batch returned 0 results (provider quirk); rerun with single-query mode succeeded.
- 395538 (HPS strictness k≥3), 395764 (Vickrey K_n), 397285 (insurance game) were screened to
  HOLD, not briefs: mechanisms exist but are research-level, not low-hanging.
- MathDB live network NOT used (429 hold standing); Google, GitHub API/raw/codeload, ScienceDirect
  and any TLS/challenge routes were not touched. Two ScienceDirect-hosted results were only used via
  public search snippets (abstract-level evidence), never fetched.

## Limitations

- Public-resolution evidence is abstract/search-level except where a retained PDF body is explicitly
  cited (394896, 394888, 396813). A root-side acceptance review should re-read bodies for any
  disposition it acts on.
- No exhaustive current-registry clearance is claimed for the two proposals; prior-art searches were
  bounded and timestamped 2026-10-31.
- ssat exact values are exact for n≤7 only; the n=6 vs Füredi–Kim (6) tension is unresolved here.
