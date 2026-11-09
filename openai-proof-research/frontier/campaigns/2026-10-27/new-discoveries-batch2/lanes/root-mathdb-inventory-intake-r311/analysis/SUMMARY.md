# Batch-1 MathDB technical triage — analysis / probability / geometry / optimization

Lane pi-mathdb-analysis-geometry-triage-r303. Pi GLM 5.3 Flash, standard speed, solo, no children. 2026-10-30.

## What was done
- Froze (hash-verified) root's derived index `root-mathdb-accepted-exclusions-r304/{accepted-exclusions,historical-dispositions}.json` before any use; zero ID collisions between the 36 reviewed records and the 33 accepted + 98 excluded/hold IDs (`artifacts/id-join-check.json`).
- Screened from the **pre-existing cached MathDB corpus** (10,064 unique records found repo-wide; corpus-inventory lane r301 not touched). Pool: 1,493 in-scope records; 1,266 open-status. A keyword heuristic ordered my own reading only — no tractability or novelty claim rests on it.
- **36 literal statements technically reviewed** (full official record JSON fetched 2026-10-30 from mathdb.com, hashed; excerpts insufficient). Dispositions in `dispositions.json`.

## Dispositions (36 records)
- **7 shortlist** (ranked): 371202 Fibonacci minima distribution; 368302 weighted fifth-order CLT; 338289 Wronskian-Hermite integrality; 352751 four-pair gamma-ratio continued fraction; 325346 Bernoulli–Euler unimodularity; 372594 D'Arcais positivity; 346879 finite Kishore.
- **3 exclude_resolved** on the record's own text: 331730 (proved by Chen–Wang–Xie), 346160 (proved per source abstract), 373493 (solved, r'=r/2, Nour–Stern–Takche). Proving bodies not read here.
- **7 reject_low_hanging**: 323777 (equivariant topology), 326447 (thin-shell family), 327210 (strengthens affine plank), 330065 (implies Real Polarization Problem), 365602 (equivalent to real HFP), 338315 (deep multilinear program), 349722 (contains an open p=1 case).
- **19 queue** (12 medium, 5 low, 2 medium-hard): 367446, 350454, 341821, 335996, 339232, 369310, 375786, 371313, 372317, 354950, 368115, 322099, 344201, 343282, 344842, 338324, 339275, 376378, 365861.

## Highlights of bounded decisive work already done
- **371202**: source is arXiv:2510.24882v5 (fetched, hashed) and labels the claim **Conjecture 8** — live. 600k-sample exact-integer density simulation (bi-infinite minimum, helper-guarded) gives P(0)=P(1)≈0.2086, P(2)≈0.1873, P(3)≈0.0597 vs claimed 0.25/0.1476/0.0628 — systematic mismatch ~100× sampling error while P(n)=P(1−n) holds exactly. The source formula (13) also sums to 1 over n≥0 while asserting the Z-symmetry — an internal mass inconsistency. Either a corrected exact cone-angle theorem or a literal refutation is within reach. No numpy in the guard; exact angular certification remains to be run.
- **368302**: statement-only analysis shows the conjectured Edgeworth coefficient 1 is unattainable for any compactly supported w (Cauchy–Schwarz, ∫w²/(∫w)² > 1), giving a complete counterexample route (Rademacher witness) — or, if w≡1 is admissible in the source's notation, a routine classical corollary. Both branches are clean; source body must be read first.

## Qualifications (explicit)
- Only one partial primary-body read (2510.24882 for 371202); all other rows are `statement_only`. No prior-art/novelty/registry screens anywhere (`prior_screen=not_performed`). `open` status is as of fetch time.
- The 36 IDs are a sample. Remaining unreviewed queue: 1,230 open in-scope records (`screen/remaining-queue.json`, heuristic order, head listed). MathDB-wide coverage is NOT claimed (95,669 total posts per root r305 receipts); full-corpus inventory belongs to r301.
- No shared/git/public/browser/MathDB mutations; lane writes only; counts untouched (9 additional / 39 total / next 40). No Lean, no manuscript, no sustained solving.
- Failures preserved: first two 371202 simulations had a termination bug (φ²>2 comparison) and one MemoryError at the 512MiB guard — scripts retained in artifacts/; no retry loops on any denied route; none encountered.

## Verification
`python3 verify.py` → exit 0 (all checks PASS; hash-bound records, frozen copies byte-identical to originals, evidence files retained). Separate receipt: `verification-receipt.json`.
