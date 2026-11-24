# MathDB 382287: Local antimagic chromatic number of even-by-odd flower-bouquet graphs

- Problem: https://mathdb.com/p/382287
- Source: Gee-Choon Lau, Wai Chee Shiu, M. Nalliah and K. Premalatha, “Construction of local antimagic 3-colorable graphs of fixed even size – matrix approach”, arXiv:2404.18049 (2024); journal version BICA 107 (2026), Conjecture 5.1. https://arxiv.org/abs/2404.18049
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `RFB.conj_5_1`, `RFB.conj_5_1_attained`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The new gadget was found by computer search (an exact-cover/MILP search over blade roles); it is a gadget of a known type in this literature. One related paper (Chan, Lau and Shiu, CCO 2025) was read only in abstract; its abstract covers other families, and two of its authors still pose the conjecture in 2026. Cross-model confidence 0.75, not routine 0.65. No second cross-model lane read the finished Lean: root compared the final theorem and every definition with the endpoint the Claude Opus reviewer had written (identical), and the GPT-6.1 Sol final check compared the definitions with the source and confirmed a small case by independent search.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. For every even r >= 2 and odd s >= 3 the flower-bouquet graph rFB(s) has local antimagic chromatic number 3 (Lau, Shiu, Nalliah and Premalatha, arXiv:2404.18049, Conjecture 5.1). The key new step is a computer-found 21-blade trade gadget that overcomes the parity obstruction blocking the source's construction for odd s. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $r$ and $s$ be integers, with $r$ even and $r\ge 2$, and $s$ odd and $s\ge 3$. Let $rFB(s)$ denote the flower-bouquet graph ($r$ disjoint copies of a hub joined to all vertices of $s$ disjoint paths on three vertices), and let $\chi_{la}(G)$ be the local antimagic chromatic number of a graph $G$. **The even-by-odd flower-bouquet conjecture.** $\chi_{la}(rFB(s))=3$.

## Summary of the result

For every even r >= 2 and odd s >= 3 the graph rFB(s) has a local antimagic labeling with exactly three vertex sums, so its local antimagic chromatic number is 3 (each blade contains a triangle, so 3 is a lower bound). The source proved the odd-by-odd case and posed this one; its method is blocked for odd s by a parity obstruction in the column sums of its labeling matrix. The new ingredient is a 21-blade trade gadget, found by a role-aware exact-cover search, that rebalances the parity across blades; with it the source's matrix supply and grouping extend to all even r and odd s, with ten small exceptional cases settled by explicit tables. Lean defines the literal graph (hub adjacent to every blade vertex, the two path edges in each blade), labels 1..|E| with |E| computed from the graph, the colour count over all vertices, and the chromatic number as an infimum shown to be attained.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
