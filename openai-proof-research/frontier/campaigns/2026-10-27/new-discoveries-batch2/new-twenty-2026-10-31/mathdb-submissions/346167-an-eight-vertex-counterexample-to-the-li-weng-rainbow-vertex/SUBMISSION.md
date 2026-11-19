# MathDB 346167: An eight-vertex counterexample to the Li–Weng rainbow vertex-disconnection Nordhaus–Gaddum conjecture (Conjecture 6.12 of arXiv:2004.06285v2)

- Problem: https://mathdb.com/p/346167
- Source: Li-Weng arXiv:2004.06285v2 Conjecture 6.12; MathDB 346167
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Rainbow.mathdb_346167_literal : ¬∀ (n : ℕ) (H : SimpleGraph (Fin n)), 8 ≤ n → H.Connected → Hᶜ.Connected → n ≤ Rainbow.sourceRvd H + Rainbow.sourceRvd Hᶜ, with sourceRvd the literal least number of colours of a rainbow vertex-disconnection colouring (source 'S + x or S + y rainbow' clause for adjacent pairs)`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `rainbow-counterexample-draft.pdf`
- Lean source: `lean-packet.tar.gz`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: published 2021 source body and 2024 Weng journal body unread (arXiv and author-hosted versions read); seven OpenAlex citing records read or screened, not all journal bodies; no thesis body clearance; Google Scholar, MathSciNet and zbMATH not consulted trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; the audit covers the 168 local declarations (axioms and metadata), not a full upstream closure inventory; the exact values 4 and 3, the order-8 catalogue count and the order-9 failures are ordinary mathematics or computation, not Lean claims; the catalogue count relies on McKay's public catalogue not_claimed: Separate credit for the order-9 failures or the catalogue statistics; A corrected general lower bound; Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the Li-Weng Nordhaus-Gaddum type conjecture that the rainbow vertex-disconnection numbers of a connected graph and its complement sum to at least the order, for order at least 8. A connected 8-vertex graph with connected complement has values 4 and 3, summing to 7; 74 of the 9888 order-8 classes fail, and three one-vertex extensions fail at order 9, so the threshold is not merely off by one. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Li and Weng, Further results on the rainbow vertex-disconnection of graphs, arXiv:2004.06285v2 Conjecture 6.12 (5.12 in v1; Bull. Malays. Math. Sci. Soc. 44 (2021)): rvd(G) + rvd(Ḡ) ≥ n for connected G, Ḡ of order n ≥ 8. False: an explicit connected 8-vertex graph G (masks 202,225,232,149,232,22,23,31) with connected complement has rvd(G) = 4 and rvd(Ḡ) = 3, sum 7. Supporting evidence: 74 of the 9,888 eligible order-8 isomorphism classes fail, and three connected one-vertex extensions fail at order 9 (sum 8 < 9), so the threshold is not merely off by one.

## Body (paste into the MathDB body field)

Use the written proof in this folder: rainbow-counterexample-draft.pdf. The complete Lean source is in lean-packet.tar.gz.
