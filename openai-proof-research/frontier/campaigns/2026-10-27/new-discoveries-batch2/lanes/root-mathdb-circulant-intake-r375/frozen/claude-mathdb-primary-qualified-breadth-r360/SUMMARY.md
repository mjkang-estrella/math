# claude-mathdb-primary-qualified-breadth-r360

The lane worked solo with no children. It reviewed exactly the fifty IDs reserved in
`root-mathdb-gram-intake-r359/reserved-ids.json`. No IDs were changed, no MathDB
requests were made, and no git, shared, index, ledger or count files were touched.
The counts stay 9 additional / 39 total / next 40.

## Freeze (before any statement was read)

`work/freeze.py` produced `freeze-receipt.json` and `input-bindings.json` (144 flat
original references; no corpus or history copies). It verified, in place:
- r359 manifest: 36 entries, exact payload-set equality, receipt PASS, and 30
  bindings checked on both the original and the copy.
- r355 manifest: 44 entries.
- The twenty r301 corpus chunks, against the immutable inventory manifest.
- The r304 manifest: 6 entries, including `accepted-exclusions.json` and
  `historical-dispositions.json`.
- The helper guard hash.

Disjointness:
- The 50 IDs equal the queue order exactly.
- Overlap with the 533 reviewed IDs: 0.
- Overlap with the 50 active r355 (Sol r356) IDs: 0.
- 404067 and 364119 are absent and were not revisited.
- r304 registry hits for the 50 IDs: none.

## Coverage of this batch

| Measure | Count |
|---|---|
| Statement reviews (literal corpus statement read, sha256 per row) | 50/50 |
| Primary-body reviews (retained, hashed, text-extracted) | 5 |
| Proof-body applicability | 368940 and 372627 complete; 372628 lower bound; 367397 independent replay of a published result |
| Novelty cleared | 0 |
| Credit | 0 |

The five primary-body reviews are 367396, 367397 (plus successor), 368940, 372627 and
372628.

Dispositions (`dispositions.json`):

| Disposition | Rows |
|---|---|
| park-hard | 23 |
| famous-hard | 9 |
| park-medium | 5 |
| publicly-resolved | 4 |
| promising-brief | 3 |
| park-finite-data-tail | 2 |
| vague-record | 2 |
| incomplete-record | 1 |
| known-theorem-misfiled | 1 |

The four publicly resolved rows are 362073, 367396, 367397 and 376061. An open label
or empty solution list was never treated as novelty.

## Results worth root attention (none claimed new; all need independent review)

1. **368940** (Rabinowitz–Suppa Conjecture 1, centroid-preserving center is X2).
   - Complete short ordinary proof in `briefs/368940.md`. Put Φ = X − G. Then
     Σ over the four 3-subsets of any 4-set of Φ is 0. Seven concyclic points and the
     explicit inverse of W_{3,4}(7) (coefficients 1/4, −1/12, 1/12, −1/4) force
     Φ ≡ 0.
   - This holds for any symmetric point-valued triangle function, and the hypothesis
     is needed only on convex cyclic quadrilaterals.
   - Scope caveats: the vertex-centroid reading and the universal reading are both
     forced. The pointwise reading is false for parallelograms. Partially defined
     centers are discussed in the brief.
   - Routine-ness risk is high.
2. **372627** (Holub–Kopřiva Conjecture 11, C_n(1,3)).
   - Certified: for every n ≥ 19, λ(3,2,1) = 11 iff 12 | n, otherwise λ ≥ 12. With
     the independently replayed upper bound, λ = 12 for even n ≥ 142 with 12 ∤ n.
   - The 12-label window graph has 152 states. Its only cycles are two 12-cycles,
     f(i) ≡ c ± 5i (mod 12).
   - Cross-checked by brute force on the actual circulants.
3. **372628** (Conjecture 25, C_n(1,5), odd n ≥ 105).
   - The 14-label window graph has 110,672 states, and every SCC period is even, so
     no odd n ≥ 31 has a span-13 labeling. The brute force agrees at n = 31 to 45
     and at n = 105.
   - The upper bound λ ≤ 14 is source Theorem 24. The independent replay failed
     under the caps (failures.md).

**367397** was proved here independently and then found to be already published:
Shtrezi, arXiv:2606.17447v1, 13 Jun 2026. Credit 0. The proof is kept in `replays/`.

Leads outside this reservation, not investigated and only for root:
- Holub–Kopřiva Conjecture 20 (C_n(1,4)) and Bosma et al. Conjecture 6
  (S_{1,g,g+d}) have no MathDB record in the r301 corpus.
- The same transfer-matrix method would apply to Conjecture 20.

## Evidence distinctions

- "record-only": the corpus statement was read; no source body.
- "record-plus-search-snippet": additionally a bounded web-search summary. This is
  secondary and was not retained as primary.
- "primary-body-read": the PDF was retained and hashed, and the relevant section was
  read.

Resolution proof bodies were not audited for any row; the successor proof for 367397
was not audited. Novelty is uncleared everywhere. Prior-art searches were bounded:
- arXiv API;
- arXiv author feeds;
- WebSearch, five standard and two extended queries.

Not checked: the published journal versions, citing papers after the source dates,
and MathDB solution pages (429 HOLD).

## Files

- `records.json`: the 50 literal corpus rows, with path, line and statement sha256.
- `dispositions.json`, `proposals.json`, `briefs/` (3), `replays/` (1).
- `sources/`: one directory per retrieval. `source-provenance.json` has URL, UTC,
  status, size and sha256 for each.
- `work/`: freeze, extract, fetch and build scripts, plus extracted text.
- `checks/`, `runs/`, `certificates/`, `bounded-checks.json`, `failures.md`.
- `manifest.json`: sha256 and size of every file except itself and
  `verification-receipt.json`.
- `verifier-negative-tests.json`: five tamper tests on temporary copies, all as expected.
- `verify.py`: fails nonzero. It re-hashes the payload, re-verifies the originals,
  the corpus and the registries in place, recomputes statement hashes from the
  corpus, regenerates the certificates, and writes `verification-receipt.json`.
