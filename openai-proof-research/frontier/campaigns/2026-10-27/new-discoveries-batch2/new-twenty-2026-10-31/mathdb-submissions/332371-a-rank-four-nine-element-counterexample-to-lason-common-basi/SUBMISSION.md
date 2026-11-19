# MathDB 332371: A rank-four nine-element counterexample to Lason common-basis conjecture

- Problem: https://mathdb.com/p/332371
- Source: Lason arXiv1601.08199v2/v3 Conjecture13; Lason arXiv1601.08199v4/v5 and Selecta Math27(2021)18 Conjecture2.5 DOI10.1007/s00029-021-00633-6
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `CommonBasis332371.counterexample`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `source-only-proof.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded primary-body, current-registry and history comparison; not global priority certification. remaining_literature_limits: Unindexed specialist counterexample or reduction not ruled out; No complete citation/external-library/deleted-history semantic clearance; MathDB live comments/solutions unread; Regular-matroid reconfiguration technical body not completely audited trust_limits: External prebuilt upstream oleans trusted; no full source-to-olean attestation; leanchecker shares Lean installation; RSS sampled child leader only, not transient-peak or aggregate-cgroup bound; Final replay used isolated private HOME rather than host HOME; all required stages passed; Portable replay utility is an evidence harness, not independently security-audited; use new disposable work directory not_claimed: Minimality; New underlying matroid; Simple-matroid counterexample; White conjecture refutation; Infinite family; Worldwide priority; Publication or journal review
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the Lason common-basis conjecture in its printed scope, at k = 2 and rank 4. An explicit rank-4 matroid on the nine elements 0 through 8, with x = 1 and y = 6, admits partitions of both E-x and E-y into two bases, but no choice of the two partitions shares a common base; parallel elements are allowed, exactly as the source permits. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

An actual rank4 matroid on9 labeled elements, with k2 and x1,y6, has two-base partitions of both deletions but no choices of such partitions share a base. Parallel elements permitted by source; full literal conjecture negation.

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in source-only-proof.zip.
