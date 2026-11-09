# r480 — Claude Opus 5.5 MathDB primary-qualified breadth screen (fifty reserved IDs)

Date: 2026-10-31 (UTC). Solo; no child agents. Writes confined to this lane. Accepted credit: **0**. New mathematics credited: **0**. Shared coverage and counts are not modified (still 9 additional / 39 total / next 40; the reported-review baseline is 3,283, and integrating these 50 is root's decision).

## Integrity preflight
All hashes were frozen before any scientific reading.
- **Intake r479.** All seven payloads plus verify.py were hashed at 11:51:06Z (`work/intake-prefreeze.txt`).
  - The manifest lists 199 files. All 199 match, and the only unlisted files are manifest.json and verification-receipt.json.
  - All 193 direct original/copy bindings match (`runs/check_intake.r1.txt`).
  - The upstream verify.py was NOT run.
- **Corpus (r301).** The manifest (sha 4da10b6d…) is verified in place: 128/128 files including all 20 corpus chunks, plus the 8 separately listed frozen_inputs (`runs/check_corpus.r1.txt`). The corpus was not copied.
- **Exclusions.** r304 accepted-exclusions.json and historical-dispositions.json were hashed at 11:52:15Z; they match the r301 frozen copies. The r363 DECISION.md and disposition.json were hashed at the same time (`work/exclusions-prefreeze.txt`).
- **Deduplication.**
  - The 50 IDs equal the queue order and are disjoint from the 50 active r476 reservations, from the five protected IDs, and from the 3,283 coverage-delta keys.
  - No ID or exact scope appears in r304 exclusions, historical dispositions, or the r363 coverage/decision.
  - Scope dedup against the 39 accepted families (`runs/scope_dedup.r1.txt`) produced two textual hits, both distinct scopes:
    - arXiv 1712.10010 appears in r363 coverage only for an earlier r320 review of its Conjecture 3.6, not Li–Wu Conjecture 1.12 (338061).
    - "permanent" matches family 14 (3×3 permanental Koteljanskii ratio for TP3), not max per(I−A) (338091).
  - The r363 Cayley exclusion concerns 364119, which is not in this batch.
- **Sources.** 48 distinct arXiv bodies were retrieved (HTTP 200, single attempt each). Their hashes were bound at download, before reading (`sources/fetch-log.txt`, `retained-sources.json`).

## Achieved coverage
| level | count |
|---|---|
| literal full record statement read and individually dispositioned | 50 |
| primary passage located and read (label line recorded per row) | 50 (48 sources) |
| source-internal proved results / definitions read where relevant | 338091, 338061, 338477, 339658, 339893, 339564, 339455, 338290, 338674, 339572, 338429 |
| whole body read | 0 |
| concluding proof / dependency audit of a public proof | 0 |
| current proof-registry check | 0 (HOLD for all; no lawful route) |
| full prior/subsumption coverage | 0 |

Dispositions:
- 3 qualified screening briefs.
- 1 retained-but-routine argument.
- 3 source-internal proof exclusions (338061, 338477, 339658).
- 1 literal/transcription defect exclusion (338091).
- 1 park, equivalent to a major open problem (339893).
- 2 HOLDs as suspected public resolutions (339115, 339269; memory only, unverified).
- 14 parked as deep or famous open problems.
- 25 parked with no tractable mechanism.

## Qualified survivors (screening stage; independent review required; prior = HOLD)
1. **338290 — counterexample** to Conjecture 3.8 of arXiv:1801.08029v2 (β_i ≤ 2w/N).
   - The source's symbol β_i is the absolute index, while its wording says "relative". Both readings are refuted with majority quotas.
   - Absolute index: (3;1,1,1,1), q=4 gives 7/8 > 6/7.
   - Normalized index: (7;1⁸), q=8 gives 127/135 > 14/15.
   - Exhaustive search: no normalized violation exists with ≤ 8 players and weights ≤ 8.
   - Brief: `briefs/P1-338290-banzhaf-counterexample.md`.
2. **339564 — proof** of Conjecture 4.4 of arXiv:1806.06821v2: d(Γ_n(1,n/2−1)^ab) ∈ {1, 2, 3} according to (n,16).
   - Method: per-prime gcd(t^n−1, 1+t+t^{m−1}) over F_p, order-8 roots over F_3, and prime divisors of the Lucas expression L_m+2.
   - Independent integer SNF check agrees for all 52 admissible n ≤ 160.
   - Side finding: the printed Theorem 4.2 order formula fails for n ≡ 0 mod 4. The corrected 3(L_m+1+(−1)^m) matches all 52 cases.
   - Brief: `briefs/P2-…`.
3. **337963 — proof** of Conjecture 49 of arXiv:1712.05883v1, with the explicit bound max resistance ≥ (diam−2)/6.
   - Method: every hub switch yields a 3-edge u–v cut, then Nash-Williams. The hub walk gives diam ≤ s+2.
   - Validated exhaustively for m ≤ 14 (8,190 instances) and on 300 random instances.
   - Scope objection: the source has no explicit definition of "linear 2-tree"; the standard one was used.
   - Brief: `briefs/P3-…`.

**Retained, not qualified:** 339455 (`briefs/R1-…`). It has a complete short proof, but the proof is a routine adaptation through an explicit classical bridge (Taylor 1981 switching connectivity plus a one-line Lipschitz lemma).

## Notable record/source defects (no credit)
- **338091:** the source's own Lemma 4.4 contradicts the printed conjecture (6−4σ vs 6−2σ). The record also misstates "row-substochastic"; the source uses doubly substochastic.
- **338429:** the record's "solved" quote is misattributed.
- **338674 / 339572:** the "solved" labels refer only to special or variant cases.
- **339895:** the record's "equivalently" sentence is wrong.
- **339115:** the record's quantifiers go beyond the source's parenthetical remark.
- **340001:** notation drift (FJ_1, B_n^{(1)}).

## Evidence limits
- No registry, successor or subsumption search was done for any row. Novelty is HOLD everywhere, and "open" labels are not taken as evidence.
- Proof bodies were not audited for the three source-internal exclusions.
- Bounded runs are sanity checks, not proofs.
- Disclosed process deviations F01–F03 (`failures.json`): unguarded Python calls for an import check and for the first receipt assembly (the verifier runs themselves were guarded), and transient /tmp output from a dry run.

## Files
- `dispositions.json`: exactly 50 rows, carrying the literal statement, chunk+line, canonical/statement hashes, evidence levels, and accepted_credit=0.
- `proposals.json` and `briefs/`.
- `retained-sources.json` and `sources/`.
- `bindings.json`: flat references to the actual originals.
- `failures.json` and `failures/`.
- `scripts/` and `runs/`.
- `manifest.json`: covers everything except manifest.json and final-receipt.json.
- `verify.py` and `final-receipt.json`.

Integrity PASS is not a mathematics or novelty PASS.
