# MathDB 382260: Gago–Coroničová-Hurajová–Madaras conjecture on low-betweenness uniform graphs

- Problem: https://mathdb.com/p/382260
- Source: Babak Ghanbari, David Hartman, Vít Jelínek, Aneta Pokorná, Robert Šámal and Pavel Valtr, “Structure of betweenness uniform graphs with low values of betweenness centrality”, arXiv:2401.00347 (2023). https://arxiv.org/abs/2401.00347
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `Betweenness.lowBUG_complement_equal_stars`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Credit the six authors of the source: the MathDB record's title names Gago, Coronicova-Hurajova and Madaras, whose different conjecture the source disproved. A close call on routineness: the argument is the source's Theorem 17 with Jensen's inequality and one new lemma, although the authors had Theorem 17 and asked for a wholly different approach (cross-model confidence 0.65, not routine 0.65). The journal text (Discrete Applied Mathematics, 2026) is unread beyond a preview, which still lists the conjecture as open; the journal wording says 'at least two' stars, which is automatic for a connected graph on at least two vertices. One sanity value in the cross-model review was wrong (it gave the betweenness of the 5-cycle as 1/2; under the source's unordered normalization it is 1); the Lean guard theorem uses the correct value, and the GPT-6.1 Sol final check confirmed the definition by enumerating all 996 connected graphs on up to seven vertices. No second cross-model lane read the finished Lean: root compared the definitions and the theorem with the endpoint that reviewer had written.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. A betweenness-uniform connected graph whose common betweenness value is less than 1 is the complement of a disjoint union of equal stars. This is Conjecture 2 of Ghanbari, Hartman, Jelinek, Pokorna, Samal and Valtr on betweenness-uniform graphs. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $G$ be a **low-betweenness BUG**, meaning a betweenness-uniform graph whose betweenness value is less than $1$. Write $\overline{G}$ for its complement. **Gago–Coroničová-Hurajová–Madaras conjecture.** If $G$ is a low-betweenness BUG, then its complement $\overline{G}$ is a disjoint union of stars of the same size. This would classify the low-betweenness betweenness-uniform graphs and show that the construction from disjoint unions of equally sized stars yields all such examples. The conjecture is presented as open in the source.

## Summary of the result

A connected graph in which every vertex has the same betweenness centrality, with that common value below 1, is the complement of a disjoint union of stars K_{1,l} of one common size l. This is Conjecture 2 of Ghanbari, Hartman, Jelinek, Pokorna, Samal and Valtr (the MathDB record's title credits other authors, whose different conjecture that paper disproved). The source proved the statement for components that are themselves uniform (its Theorem 17) and excluded small l case by case. The proof here replaces uniformity by Jensen's inequality in the source's excess argument and adds one new lemma, that every vertex is close to at least l + 1 edges of the complement, together with the equality case. Lean defines betweenness by counting shortest walks over unordered pairs of other vertices, proves the shortest-walk counting the argument needs, and includes guard theorems against the wrong normalizations.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
