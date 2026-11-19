# MathDB 330264: Three spectral invariants do not determine geodesic growth of tree-based right-angled Coxeter groups: a counterexample to Ciobanu-Kolpakov Conjecture 1.3 (arXiv:1504.02774)

- Problem: https://mathdb.com/p/330264
- Source: Ciobanu-Kolpakov arXiv:1504.02774v3 Conjecture 1.3 (J. Algebraic Combin. 44 (2016)); MathDB 330264
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `MathDB330264.conjecture_false : ¬ MathDB330264.Conjecture, where Conjecture := ∀ n m (T : SimpleGraph (Fin n)) (U : SimpleGraph (Fin m)), T.IsTree → U.IsTree → TripleCospectral T U → ∀ k, geodesicGrowth T k = geodesicGrowth U k; TripleCospectral = equal characteristic polynomials over Q of adjacency, complement and Mathlib line graph; geodesicGrowth k = number of length-k words that are reduced in the actual right-angled Coxeter system of the graph`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `330264-replay-fit-r2-source.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: 2016 journal version of record body unread (post-publication author arXiv v3 retains the conjecture); bounded dated citing-body and registry screens; MathDB/Palomar access denied and not retried; Google Scholar, MathSciNet and zbMATH not consulted trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; the audit covers the 874 packet declarations (axioms and metadata) plus the mechanically computed statement closure, not a full upstream closure inventory; the agreement through length 17 and the comparison with the source's own family are ordinary computation, not Lean claims not_claimed: Minimality of the 19-vertex pair; An infinite family; A new normal-form theorem; Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the Ciobanu-Kolpakov conjecture that trees whose adjacency, complement and line-graph spectra coincide have right-angled Coxeter groups with the same geodesic growth. Two explicit 19-vertex trees with all three characteristic polynomials equal have 37769749324097905710910 versus 37769749324097905710906 geodesic words of length 18. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Ciobanu-Kolpakov Conjecture 1.3: trees whose adjacency, complement and line-graph spectra coincide have right-angled Coxeter groups with the same geodesic growth. False: two explicit 19-vertex trees with all three characteristic polynomials equal have 37769749324097905710910 versus 37769749324097905710906 geodesic words of length 18.

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in 330264-replay-fit-r2-source.zip.
