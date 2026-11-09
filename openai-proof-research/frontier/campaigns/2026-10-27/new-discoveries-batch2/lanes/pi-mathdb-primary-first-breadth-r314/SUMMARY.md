# SUMMARY — pi-mathdb-primary-first-breadth-r314 (breadth checkpoint, 50 reserved IDs)

Status: COMPLETED checkpoint. All 50 reserved IDs from
`root-mathdb-inventory-intake-r311/next-breadth-ids.json` had their **full cached
statements read** from the immutable r301 corpus chunks, hash-bound **before**
reading (`source-bindings.json`; all 50 found in chunks 0002–0018, no duplicates).
No overlap with the 83 reported statement-reviewed IDs, accepted-exclusions.json,
or historical-dispositions.json (verified programmatically by scope-id intersection).
No MathDB network requests (429 hold respected). No shared/ledger/git edits.
Counts unchanged: 9 additional / 39 total; nothing here is an acceptance claim.

## Achieved coverage
- 50/50 record statements read and dispositioned (`dispositions.json`).
- Primary bodies read: **350551** only (Wagner arXiv:2104.14516 §2.6 via arXiv HTML).
- Source abstracts read: 322922, 339516, 350551 (arXiv).
- OWR/ems.press sources for 403959, 392861, 397963, 393182 etc. were **not**
  fetched (bounded run); those rows stay record-level.
- Access failure preserved: arXiv figure images for Wagner Fig. 11/12 (exact ∗/∘
  definitions) 404'd on guessed paths; not retried.

## Headline findings
1. **350551 (statement/reference mismatch, likely source-refuted).** The record's
   `references` field quotes refutation prose from Wagner §2.4 (Collins
   peak-location disproof) — unrelated to the 312-avoiding permanent conjecture of
   §2.6. But §2.6 itself reports: best recursive-family permanent at n=10 is 394,
   while 312-avoiding constructions reach per=424 (optimality proved only n≤8, so
   424 is a valid lower bound for f_312(10) regardless). If the 394 figure is the
   exhaustive max over M_10(∗,∘), the recorded conjecture fails at n=10.
   Decisive bounded check specified in proposals.json (exhaustive DP over
   M_10(∗,∘) + Ryser + avoidance verifier; sanity gates max M_8 = 120, per(A_9)=225).
2. **Five stale open labels with public resolutions found** (abstract-level;
   NOT counted as verified exclusions without body comparison):
   - 393182: kissing number dim 4 = 24 — Musin arXiv:math/0309430, Annals 168 (2008).
   - 393170: LP auxiliary functions for (8,√2) and (24,2) exist — Viazovska
     arXiv:1609.08199; Cohn–Kumar–Miller–Radchenko–Viazovska arXiv:1603.06518.
   - 403876: G(k) ≤ ⌈k(log k + 4.20032)⌉ is the main theorem of arXiv:2211.10380
     (statement matches the MathDB record verbatim).
   - 394650: b(G) ≤ 7 for non-standard actions — Burness–Liebeck–Shalev, Proc. LMS
     2008 (equality-case M24 part needs body comparison).
   - 393575: random-transposition distance phase transition — Berestycki–Durrett
     arXiv:math/0403259 (time-normalization notation differs; body comparison needed).
3. **Cheap rejections:** 19 famous/ill-posed records (L=P, PIT, GI, MCSP,
   Witsenhausen, Rudin, Erdős–Gyárfás 2^k-cycles, Serre-adjacent X_ns^+(p),
   3D-Ising-formula nonexistence, Siegel 120°, spin glasses/O(N), FPP
   Tracy–Widom, toric exceptional collections, etc.) and 8 hard-but-not-small
   records. All with preserved one-line reasons in dispositions.json.
4. **Top hypothesis rows (max 5, all unqualified):** 350551 (small counterexample
   certificate, body-read), 322922 (small DP certificate, abstract-read),
   403959 (enumeration GF), 392861 (verify recorded 4 ln(2 Opt) theorem),
   397963 (small rigidity counterexample search). Parked: 339516, 387083,
   393152, 394700, 325151.

## Residuals / exact remaining
- No IDs remain unread from the reserved 50.
- Unreconciled: 372594 remains parked outside this batch (untouched here).
- 350551: exact ∗/∘ definitions + exhaustive M_10(∗,∘) computation outstanding.
- 322922/339516: full bodies unread — rows are not solve-ready.
- 403959/392861/397963: OWR bodies unfetched — record-level only.
- Stale resolutions 393170/393575/394650: body-level confirmation outstanding.
- This checkpoint covers 50 of 95,675 known IDs; it is a coverage increment,
  not whole-corpus review.
