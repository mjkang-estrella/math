# MathDB 358647: The local weak limit of uniform random fullerenes

- Problem: https://mathdb.com/p/358647
- Source: MathDB358647; Bille, Buchstaber, Coste, Kuriki, Spodarev, arXiv 2306.01462v2, Definition 2, Eq. (3), Eq. (4), Conjecture 1
- Outcome: **PROVED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Ful.endpoint`, `Ful.localWeakConvergence`, `Ful.Helix.nonVacuous`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `fullerene-local-limit.pdf`, `fullerene-local-limit.roff`
- Lean source: `fullerene-358647-source-only.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded source-primary investigation, not worldwide priority certification. prior_limits: No citation index. The journal version J. Phys. A 58(2) (2025) 025212 is unread, so whether it keeps Conjecture 1 is unknown; if the journal version or a later paper settles the conjecture, the acceptance must be revisited. Thurston, Brinkmann and coauthors, Graver, Kardos-Skrekovski and Angel-Benjamini-Horesh are unread; the Kardos habilitation and MATCH 71(1) 99-114 are closed. Registry roots closed. trust_limits: Upstream Lean, mathlib and their oleans are trusted through pins and were not rebuilt. Reviewers are AI systems, not human referees, and the reviewers, auditor and Lean author share a model family. The auditor did not read 33 proof scripts line by line. Planarity is rendered as a genus-0 rotation system; its equivalence with topological planarity is classical and not proved in Lean. The labelled reading of uniform is not formalized. Whitney uniqueness is neither proved nor used: each class is handled through one chosen embedding. not_claimed: Worldwide novelty or publication priority; Human peer review; The labelled reading of uniform; Any rate beyond the stated bound
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: the local weak limit of uniform random fullerenes is the hexagonal lattice. For every fixed radius and rooted finite graph, the probability that the rooted ball around a uniform root of a uniform isomorphism class of fullerene graphs on n vertices matches the corresponding hexagonal-lattice ball tends to 1 or 0 according as the two balls are isomorphic; fullerenes are cubic graphs with a genus-zero rotation system, all faces of size 5 or 6. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

For every r and every rooted simple graph (K,o), along the n admitting a fullerene, the probability that the ball of radius r around a uniform root of a uniform isomorphism class of fullerene graphs on n vertices is rooted-isomorphic to the ball of (K,o) tends to 1 or 0 according as the corresponding ball of the hexagonal lattice of Eq. (3) is isomorphic to it; and the limit filter is proper. A fullerene is a finite connected cubic simple graph admitting a genus-0 rotation system with every face of length 5 or 6; balls use the strict inequality of the source.

## Body (paste into the MathDB body field)

Use the written proof in this folder: fullerene-local-limit.pdf. The complete Lean source is in fullerene-358647-source-only.zip.
