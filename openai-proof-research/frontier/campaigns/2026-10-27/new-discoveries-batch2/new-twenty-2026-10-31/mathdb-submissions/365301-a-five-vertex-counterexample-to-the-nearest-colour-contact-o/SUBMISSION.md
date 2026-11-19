# MathDB 365301: A five-vertex counterexample to the nearest-colour contact-order conjecture for two-variable Cauchy transforms of coloured graphs

- Problem: https://mathdb.com/p/365301
- Source: R. Tully-Doyle et al., arXiv:2410.10695 Conjecture 6.1; MathDB 365301
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `ContactPilot.refutationLocal : ¬ ContactPilot.SourceConjectureLocal, where SourceConjectureLocal quantifies over every n, simple graph G on Fin n, Boolean colouring, root i, reduced rational-inner certificate of the actual coloured resolvent (M^-1)_ii with M = A - zY - w(I-Y), and natural d, K, and asserts NearestWDistance G isZ i d -> 0 < K -> Even K -> HasLocalZeroSetContact (eval2 cert.numerator) (-1) 1 K -> K = 2d; HasLocalZeroSetContact is the local zero-set contact order (c, C, rho0 fixed first; lower bound for every disk zero within rho0; upper witness inside every rho in (0, rho0] with the same C), with uniqueness proved (local_contact_unique)`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `contact-draft.pdf`
- Lean source: `contact-r6-source.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: source journal body unread (ScienceDirect route excluded); Hong thesis, admissible-numerators companion and unindexed citing works unread trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; the existence-versus-uniqueness bridge to the source's analytic contact order is an ordinary argument (reviewed), not a general Lean theorem; the locality regression for the reviewer's diagnostic pair is ordinary, not Lean not_claimed: A corrected general contact-order formula for multiple w vertices; Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the contact-order conjecture of Tully-Doyle, Adlin, Thai and Tiscareno for Cauchy transforms of coloured graphs, Conjecture 6.1: the contact order at the boundary point of the pair (infinity, 0) should equal twice the distance to the nearest w-coloured vertex. A five-vertex graph with root 0 and w-coloured vertices 1 and 2 has nearest distance 1 but contact order 6, with branches of exact orders 6 and 2. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Tully-Doyle, Adlin, Thai and Tiscareno, Cauchy transforms of colored graphs in two variables, arXiv:2410.10695 (v1 2024, v2 2025), Conjecture 6.1: the contact order at the boundary point corresponding to (infinity, 0) equals twice the distance from the root to the nearest w-coloured vertex. False: the five-vertex graph with edges 01,02,03,13,24,34, root 0 and w-vertices 1,2 has nearest-w distance 1 but contact order 6 (analytic branches of exact orders 6 and 2; local maximum-branch convention of the source and of Bickel-Hong).

## Body (paste into the MathDB body field)

Use the written proof in this folder: contact-draft.pdf. The complete Lean source is in contact-r6-source.zip.
