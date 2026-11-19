# MathDB 353203: Power-domination TAR uniqueness for complete bipartite graphs: PD^TAR(K_{s,t}) is unique if and only if s ≠ 2 and t ≠ 2

- Problem: https://mathdb.com/p/353203
- Source: Bjorkman et al., arXiv:2201.01798 uniqueness conjecture; La Matematica 5 (2026) article 8; MathDB 353203
- Outcome: **PROVED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `PDTAR.mathdb_353203 (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) : TARUnique (completeBipartiteGraph (Fin s) (Fin t)) ↔ (s ≠ 2 ∧ t ≠ 2), with literal simultaneous power-domination rounds, TAR graph on PD sets with symmetric-difference-one adjacency, and TARUnique quantifying over every finite graph H without isolated vertices`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `pdtar-source.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: La Matematica journal text unread (Springer challenge page; Swarthmore 403); Bong et al. journal body read via the survey's proof chain, not directly trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; SAT logs and exhaustive lemma checks are evidence only not_claimed: Priority; Publication; Uniqueness results for other X-set parameters
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: the power-domination reconfiguration uniqueness alternative for complete bipartite graphs: the TAR invariant PD^TAR of K_(s,t) is unique if and only if s and t both differ from 2, settling the uniqueness question left open in the power-domination reconfiguration paper. A new core theorem with fort duality and cross-degree rigidity is combined with the published relabelling reduction, and the small cases are formalized too. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Bjorkman, Bozeman, Ferrero, Flagg, Grood, Hogben, Jacob and Reinhart, Power domination reconfiguration, arXiv:2201.01798, La Matematica 5 (2026): the uniqueness conjecture stated after Proposition p:K33 (still listed open in the Curtis-Flagg-Hogben survey arXiv:2406.05509v2, 2025). Proved: the new Core Theorem (for s,t >= 3, (s,t) != (3,3), K_{A,B} is the only graph on A ⊔ B with exactly its PD sets) via fort duality, pair forts, cross-degree rigidity isolating (3,3), two-sided completeness and independence; with the published TAR relabelling reduction (Bong-Carlson-Curtis-Haas-Hogben, Graphs Combin. 2023) formalized by a self-contained Hamming-isometry proof, and the source's small cases (K_2, K_{1,t}, K_{2,t} via K_{2,t}(e), K_{1,2} vs K_3, K_{3,3}) all formalized.

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in pdtar-source.zip.
