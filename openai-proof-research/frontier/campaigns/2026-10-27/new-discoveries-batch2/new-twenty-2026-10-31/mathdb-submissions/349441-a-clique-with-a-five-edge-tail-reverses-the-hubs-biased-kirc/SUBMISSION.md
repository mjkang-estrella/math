# MathDB 349441: A clique with a five-edge tail reverses the hubs-biased Kirchhoff ordering

- Problem: https://mathdb.com/p/349441
- Source: E. Estrada, D. Mugnolo, arXiv:2101.07103v2 Conjecture 4.13; J. Math. Anal. Appl. 507 (2022) 125728; MathDB 349441
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `KirchhoffReal.refuteSpec : ¬ LiteralConjecture GroupInverse spectralIndex (Lemma 4.6 spectral reading, primary substantive result); KirchhoffReal.refuteMP : ¬ LiteralConjecture Penrose pairIndex (literal (4.3) Moore-Penrose reading)`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `kirchhoff-draft.pdf`
- Lean source: `kirchhoff-source-only.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: Chaos 33 (2023) biased-Kuramoto paper only partially read; citing-work inventory not exhaustive trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; eigenvalue-to-trace identification proved ordinarily, not in Lean (the Lean spectral endpoint is the group-inverse trace) not_claimed: Global minimality (smallest spectral counterexample order in [9,11]); Any repaired physical resistance model; Credit for the source's definitional inconsistencies; Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the Estrada-Mugnolo conjectured ordering of the hubs-biased Kirchhoff indices, R_1 >= R_0 >= R_-1 with equality only for regular graphs. The complete graph K_6 with a pendant path of five edges has R_1 below R_0, and the literal Moore-Penrose reading of the indices fails there too, and already at order 5; the spectral index of the source's Lemma 4.6 satisfies the ordering on all 12103 connected graphs of orders 5 to 8. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Estrada-Mugnolo (J. Math. Anal. Appl. 507 (2022) 125728, arXiv:2101.07103) Conjecture 4.13 asserts R_1 >= R_0 >= R_-1 for hubs-biased Kirchhoff indices, with equality iff regular. The spectral index the authors computed (Lemma 4.6, n*tr of the group inverse) satisfies the ordering for all 12,103 connected graphs with 5<=n<=8 (independent review), but K6 with a pendant five-edge path has R_1 = 1696684/14035 < 370/3 = R_0. The literal Moore-Penrose reading (4.3) also fails there (515538204/7137235) and already fails at n=5, an uncredited source inconsistency.

## Body (paste into the MathDB body field)

Use the written proof in this folder: kirchhoff-draft.pdf. The complete Lean source is in kirchhoff-source-only.zip.
