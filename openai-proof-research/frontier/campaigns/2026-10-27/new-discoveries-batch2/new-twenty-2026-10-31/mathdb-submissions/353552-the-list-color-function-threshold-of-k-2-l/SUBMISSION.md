# MathDB 353552: The list color function threshold of K_{2,l}

- Problem: https://mathdb.com/p/353552
- Source: MathDB353552; Kaul, Kumar, Mudrock, Rewers, Shin, To, arXiv 2202.03431, Conjecture 5
- Outcome: **PROVED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `ListCol.tau_isTheta`, `ListCol.tau_completeBipartite_isTheta`, `ListCol.countL_ge`, `ListCol.tau_le_kB`, `ListCol.tau_gt_source`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `list-color-threshold-k2l.pdf`, `list-color-threshold-k2l.roff`
- Lean source: `list-color-353552-source-only.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded source-primary investigation, not worldwide priority certification. prior_limits: No citation index. The J. Graph Theory final of the source, DOI 10.1002/jgt.23045, returned 403, is closed and unread, so whether it changes Conjecture 5 is unknown. arXiv 2505.05662, 2509.16733 and 2607.16810 were read in part only. Registry roots closed. trust_limits: Upstream Lean, mathlib and their oleans are trusted through pins and were not rebuilt. Reviewers are AI systems, not human referees, and the reviewers and the final Lean author share a model family; the formal proof follows the first reviewer's route. Colours are Finset Nat; the relabelling and instance-independence bridges exist only in the auditor's control modules. The every-larger-m clause is separated from equality at k only for k below the chromatic number, since a separation at k >= chi would answer the source's open Question 2. not_claimed: Worldwide novelty or publication priority; Human peer review; The sharp constant, which is not formalized; Any statement for K_{s,l} with s >= 3 beyond the hand-checked remark
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: the list colour function threshold of the complete bipartite graph K_(2,l) grows like the square root of l. The smallest k from which every k-list assignment admits exactly as many proper colourings as the chromatic polynomial is Theta of sqrt(l) in the number of vertices l; moreover, for m >= 4 and 2l <= (m-1)^2, every m-assignment has at least m(m-1)^l + m(m-1)(m-2)^l colourings. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

tau(K_{2,l}) =Theta[atTop] sqrt l over l in Nat, for tau the list color function threshold, the smallest k >= chi(G) with P_l(G,m) = P(G,m) for every m >= k, defined by sInf over a set proved nonempty, on the actual mathlib completeBipartiteGraph (Fin 2) (Fin l). Also: for m >= 4 and 2l <= (m-1)^2, every m-assignment of K_{2,l} has at least m(m-1)^l + m(m-1)(m-2)^l proper list colourings.

## Body (paste into the MathDB body field)

Use the written proof in this folder: list-color-threshold-k2l.pdf. The complete Lean source is in list-color-353552-source-only.zip.
