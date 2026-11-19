# MathDB 352303: Extremal trees for the biharmonic index

- Problem: https://mathdb.com/p/352303
- Source: MathDB352303; Z. Lin, arXiv 2110.09931, Conjecture 5.3; AIMS Mathematics 7(4) (2022) 6050-6065, Conjecture 5.3; Wei-Li-Yang arXiv 2110.02656v2 Problem 6.3
- Outcome: **PROVED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `BiH.bh_endpoint`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `biharmonic-index-trees.pdf`, `biharmonic-index-trees.roff`
- Lean source: `biharmonic-352303-source-only.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded source-primary investigation, not worldwide priority certification. prior_limits: No citation index. Zhou LAA 429 (2008), Liu-Liu AML 24 (2011), Das-Xu-Liu LAA 439 (2013) and Chen-Das DM 338 (2015) are unread; Wei-Li-Yang cite them and leave the tree problem open. MATCH 91(2) 285-286 is closed, unread and unidentified; if it bears on this conjecture the acceptance must be revisited. Gutman 2004, A New Hyper-Wiener Index, was read in abstract only and its full text is closed after HTTP 418. Modified hyper-Wiener indices in the literature are the Laplacian coefficient c_{n-3}, not the squared family, and no printed extremal theorem for the squared family was found. Registry roots closed. trust_limits: Upstream Lean, mathlib and their oleans are trusted through pins and were not rebuilt. Reviewers are AI systems, not human referees, and the reviewers and the final Lean author share a model family. Only the spectral form of BH is formalized; the source also prints the double-distance form as equal. not_claimed: Worldwide novelty or publication priority; Human peer review; Any statement about the sum of lambda^(-k) for k other than 2; The unreviewed star-side law as a separate result
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: among trees on n >= 5 vertices, the star minimizes and the path maximizes the biharmonic index, defined as the vertex count times the sum of the inverse squares of the nonzero Laplacian eigenvalues. Equality on the left holds only for the star and on the right only for the path, up to isomorphism. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

For every n >= 5, every finite vertex type V with card V = n and every tree G on V: bh(star on n vertices) <= bh G <= bh(path on n vertices), with equality on the left iff G is isomorphic to the star and on the right iff G is isomorphic to the path, where bh G = (card V) times the sum over nonzero Laplacian eigenvalues of lambda^(-2).

## Body (paste into the MathDB body field)

Use the written proof in this folder: biharmonic-index-trees.pdf. The complete Lean source is in biharmonic-352303-source-only.zip.
