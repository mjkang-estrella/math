# T333E107 contribution review r2

**Verdict: TECHNICAL, conditional on correctness.** There is no
substantial-contribution PASS and no proof-gate decision. Count credit is
zero, no R-number is assigned, and no acceptance is entered. The campaign
remains 18/20 as supplied. The parent integrates and decides.

## Files

- `review.md`: the standalone review. It covers the exact target, the paid
  source contracts, an operation-level reduction R1–R7, the strongest
  case for substantiality, a gap assessment, same-family comparison, and
  a reassessment of the r1 drafts and all carried objections.
- `paid-unpaid-comparison.md`: a row-by-row table with exact source labels
  and line numbers, plus qualified primary comparisons.
- `reading-limits.md`: the actual semantic extents, the deliberately unread
  files (r3, parent disposition), and integrity/rights notes.
- `checks.py` / `checks.json`: finite checks.
  - Exact rational replay of the author's hostile two-jet.
  - Exact four-way equivalence test of the paid transversality.
  - A float model contrasting orthogonal folding with oblique cancellation.

  These are illustrations, not proofs.
- `status.json`: the machine-readable no-count boundary.
- `verify.py`: a read-only verifier. It requires the detached manifest
  digest; performs no writes, network access or payload execution; checks
  exact payload membership and external anchors (author packet, context,
  r1 drafts and companions); checks the complete 13,223-entry tree; and
  re-authenticates the author's 13 pinned source blobs.
- `build_manifest.py`: writes `manifest.json` and `seal.sha256`.
- `integrity_controls.py` / `integrity-controls.json`: the positive and
  negative controls, run on copies in a temporary directory.

## Verify

Read `verify.py` first, then run:

    python3 -I verify.py --expected-manifest <DETACHED_SHA256> --repo-root /home/mj-kang/Documents/Dev/math/openai-proof-research

Use the digest given in the parent-facing handoff. `seal.sha256` is only a
convenience copy. Success authenticates bytes, not mathematics.

The integrity-controls receipt was produced against the pre-receipt
manifest named inside it. Adding the receipt required a final reseal. The
final manifest was then re-verified, and all controls were rerun against
it outside the bundle; the results are reported in the handoff.
