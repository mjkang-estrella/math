# Conditional Bessel release preparation

The candidate is not accepted. Its independent final review and the parent's
substantive eligibility decision remain pending. This directory contains only
release infrastructure, outside the 56-file frozen review target.

`release_tools.py check-inputs` checks the frozen manifest and the retained
87-declaration / 8-module parent receipt. It does not establish novelty or
replace independent review.

After the review completes, read the actual report, provenance, independent
receipt, all findings and strongest objections. If the decision is HOLD/FAIL,
do not assemble or count. Only if all six gates pass and the parent adopts the
eligibility assessment, write a new concrete decision (do not overwrite this
pending template), bind the actual review bytes, and use `assemble`.

Then rebuild the release paper with its operational-status overlay, render and
read all three pages, and update paper-qa.json with current hashes and actual
parent_release_all_pages_read=true. The mathematical text and all Lean source
bytes must remain the reviewed bytes. `archive` verifies original-byte retention
and deterministic manifest-only packaging, extracts once to a new directory,
and explicitly leaves acceptance pending. Run verify_candidate.py against that
fresh extraction with the pinned Lean and packages; read every endpoint/type/
axiom report and require clean logs and a receipt identical to both prior ones.
Only afterward may the parent write acceptance.json and the shared ledger.

No archive globbing, prebuilt Lean objects, claims of worldwide priority, or
separate helper/witness credits. Rerun the complete collection audit after any
acceptance and report exact source scope rather than '30 MathDB conjectures'.
