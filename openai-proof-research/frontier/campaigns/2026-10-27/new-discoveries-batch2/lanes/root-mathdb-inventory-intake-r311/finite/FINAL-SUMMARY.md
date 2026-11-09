# Final summary — MathDB finite-arithmetic technical triage r302 (batch 1 handback)

Lane: `lanes/pi-mathdb-finite-arithmetic-triage-r302` · Solo, no children · UTC 2026-10-30

## Scope and honesty limits

- **Screened 48 distinct MathDB records** by literal full statements retained from local
  caches (no live fetch — API returned 429; see failures.md). Coverage is a **bounded
  subject sample** (48 of ~293 open, unflagged, in-scope cached full records), never a
  whole-database claim. Counts 9 additional / 39 total / next 40 untouched.
- **No primary proof body was read.** Every promotion carries a mandatory primary-read
  step; source fields are record-metadata level only.
- The interrupted `sol-mathdb-technical-shortlist-r300` lane **does not exist on disk**;
  there was nothing to resume (recorded in failures.md).
- All inspected IDs were joined to frozen `root-mathdb-accepted-exclusions-r304`
  (accepted families, first-30 publications, historical exclusions/holds) — no inspected
  record carries an accepted-family flag; r305 retrieval receipts frozen before use.

## Deliverables

| Artifact | Path |
|---|---|
| Input/source bindings (sha256) | `administrative/input-bindings.json` |
| Pool index (443 unique cached full records, 168 in scope) | `records/pool-index.json` |
| Screening batch (48 literal statements + metadata) | `screening/batch1-statements.json` |
| Per-record dispositions (48, machine-readable) | `screening/dispositions.json` |
| Shortlist (10 candidates, full fields) | `shortlist/shortlist.json` |
| Counterexample witness data (375237) | `screening/witness-375237.json` |
| r306 intake format copy (48 rows) | `intake-proposals.json` (also copied to `root-mathdb-hypothesis-intake-r306/proposals.json`) |
| Failures and access log | `failures.md` |
| Manifest / verification | `manifest.json`, `verification-receipt.json` |

## Disposition totals (48)

10 shortlisted · 15 rejected/excluded (4 resolved-by-source: 372418, 372594, 365581, 353227;
1 likely resolved-by-source: 372787; 3 prior-overlap CA115/CAPeriods: 375267–69; 3 deep
programs: 337807, 348539, 374706/366993-class; 2 routine/ill-posed: 349272, 336487;
1 deep arithmetic: 377365; 1 operator-algebra depth: 406427) · 23 uncertain/queued
(incl. 2 garbled statements: 353474, 380719).

## Shortlist (ranked; all pending primary-source confirmation)

1. **375237** Subtraction-Nim period claim — literal "period equals one of a+b, b+c, c+a"
   numerically refuted by S=(1,3,5) (eventual period 2; 37 witnesses). Bounded
   counterexample; only dependency is confirming the literal wording in arXiv:2606.11658 /
   2312.02426 (if the source says "divides", the refutation dies).
2. **323014** Nim/zero-position period equality — survived my falsification search
   (no violation for |S|≤3 in window); proof for |S|≤2 or larger-scale counterexample.
3. **358561** Coefficient GCD of c_m(c_1) is a power of two (Painlevé III recurrence).
4. **341578** Stern recurrence matrices: explicit eigenvalue multiplicities + semisimplicity.
5. **327048** Sills–Zeilberger P_{01r}(N): monic/alternating/convex, roots {0,1}.
6. **365538** Louboutin Laurent-polynomial identity — must first check it is not already
   proved inside 2410.21158 (high risk).
7. **371523** Bonse threshold Ψ(x) explicit values — my bounded check consistent with
   claims (i)–(ii) in-window (max failing n=20 resp. 148); (iii)–(v) need bigger sieves;
   root may classify as routine parameter computation.
8. **380137** Shi distance-enumerator unimodality (open since 2006).
9. **381656** Finiteness of odd n with s(n)=s(n²)=14 or 15 — method extension from 9–11.
10. **378937** Xin's second determinant factorization (odd n) — statement must be re-read
    from source (cache mangled).

## Remaining review queue

~245 open in-scope cached full records not yet inspected (pool-index.json, status=open,
no campaign flags), plus 23 uncertain/queued records above. Live MathDB fetching remains
unavailable from this lane pending rate-limit recovery; next batch should prefer cache +
one polite probe, never a retry loop.

## Bounded computations performed (all guarded, caps respected)

- `scripts/check_nim2.py`: period-equality search — no violations in window.
- `scripts/dump_witness.py`: 37 counterexample witnesses for 375237 (artifact saved).
- `scripts/check_bonse2.py`: Bonse window consistency — consistent for (i),(ii); window
  only; no claim beyond n<6000.
- `scripts/check_misc3.py`: Delannoy D² real-rootedness — non-real roots under both
  boundary conventions; recorded as convention conflict on 375724 (not a disposition).
