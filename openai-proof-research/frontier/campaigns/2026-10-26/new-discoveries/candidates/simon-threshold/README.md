# Simon threshold convexity

One combined resolution of the explicit threshold-convexity question in Simon,
arXiv:2012.11018v2, Section 3, page 5, final paragraph. For every gamma>1,
the literal infimum over admissible beta>0 is convex on (0,1/gamma).
The main MathDB 349140 complete-monotonicity equivalence is NOT resolved.

Read paper.pdf, formal/SourceConvex.lean, NOVELTY.md and reviews/final/review.md.
The independent review finds all five gates PASS and judges the result substantive
and eligible, while expressly recording its short, standard-tool-based character.
The new reduction is the exact literal-infimum/perspective-supremum identity.
Perspective convexity and supremum convexity are standard, credited ingredients.

All 58 reviewed original files are preserved, with reviewed-file-locations.json
mapping their original names to stored bytes. Release-paper edits remove only
operational draft-status prose; no mathematical claim or Lean source changes.
PROOF.md contains an additional informal strict-curvature route which is NOT
part of the formal result, release-paper theorem, or discovery credit.

Replay with pinned Lean 4.34.1 and the packages in verification/pins.json:
python3 verification/verify_candidate.py . --lean-bin /absolute/path/to/lean --packages /absolute/path/to/.lake/packages

The 26 declarations in 5 modules use only propext, Classical.choice, Quot.sound.
Parent and independent receipts are byte-identical. Extracted replay is required
before acceptance; acceptance.json and the campaign ledger record that final step.
Historical credit-zero/pending snapshots remain preserved as historical records.

No global priority claim. The publisher body and four closed citing bodies remain
unread; the bounded prior-art coverage and exact limits are documented.
