# MathDB 352496: The Polynexus ordered-pair formula for the contiguous-diagonal rook submonoid

- Problem: https://mathdb.com/p/352496
- Source: Fikioris-Fikioris, A subsemigroup of the rook monoid, arXiv2111.01863v3, sections2-4 and8, equations53-55/Remark3/Conjecture1; Publisher body DOI10.1007/s00233-022-10302-5 independently compared
- Outcome: **PROVED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `polynexus_literal; source set bridge PNZ_source; polynexus_integer and polynexus_rational; polynexus_one`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `polynexus-proof.pdf`, `polynexus-proof.md`
- Lean source: `polynexus-source-only.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded primary-body/source-version/current-registry/subsumption investigation; worldwide priority not certified. remaining_literature_limits: No complete worldwide/citation/registry-tree/deleted-history clearance; OEIS A083200 denied and not retried; Live MathDB comments/solutions not cleared; Unindexed/inaccessible prior solutions or reductions remain possible trust_limits: Pinned prebuilt upstream trusted; no full upstream rebuild/attestation; leanchecker shares pinned Lean installation; RSS sampled, not universal cgroup/aggregate concurrency peak guarantee; Strict whole historical process compliance not asserted not_claimed: Formula for the full rook monoid; Count of distinct product outputs; Noncommutativity at n1 or canonical n0; Bundled exported Lean Submonoid/general-semiring transport interface; Worldwide priority/publication/journal peer review; Separate credit for helpers or canonical boundary extensions
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: in the rook submonoid consisting of zero and the n-by-n 0/1 matrices supported on a single contiguous block of one integer diagonal, the number of ordered pairs of nonzero elements whose ordinary matrix product is nonzero equals ((n+1)^7 - n^7 - (n+1)^3 + n^3)/120, for every positive n. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

For positive n, M_n is zero plus the n-by-n 0/1 matrices X(d,k,m) supported on one contiguous block of one integer diagonal, with printed signed bounds. psi counts ORDERED pairs of nonzero operands whose ordinary matrix product is nonzero. Then 120 psi(n)=(n+1)^7-n^7-(n+1)^3+n^3. The n1 case is proved; all-Nat integer/rational theorems and independent n0 controls are a canonical extension, not separate credit.

## Body (paste into the MathDB body field)

Use the written proof in this folder: polynexus-proof.pdf. The complete Lean source is in polynexus-source-only.zip.
