# MathDB 337410: The incremental conjecture for set multipartite Ramsey numbers

- Problem: https://mathdb.com/p/337410
- Source: Claudia J. F. Gonçalves, Emerson L. Monte Carmelo and Irene N. Nakaoka, “Projective planes and set multipartite Ramsey numbers for C_4 versus star”, arXiv:1710.06383 (2017). https://arxiv.org/abs/1710.06383
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `MultipartiteRamsey.conj_2_3`, `MultipartiteRamsey.ramseyProp_exists`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Prior art not fully cleared: three texts by the same authors could not be read by any lane (their 2020 paper in Brazilian Journal of Development, their 2021 paper in Procedia Computer Science 195, and the first author's 2019 thesis; the sites refuse automated clients). The abstracts that could be read mention no such step bound; the cross-model reviewer puts 'not public' at 0.85. Read them before publishing. The MathDB record says 's-partite'; the source means c classes of s vertices each, which is what Lean states. The proof is short (about fifteen lines of idea) and elementary; the cross-model reviewer rates it not routine at 0.6 and overall about 0.5. No second cross-model lane read the finished Lean: root compared the definitions and the theorem with the endpoint that reviewer had written and found them identical.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. For all s >= 2 and n >= 2, M_s(n+1) <= M_s(n) + 1 for the set-multipartite Ramsey number of C_4 against the star K_{1,n} (c classes of s vertices). This is Conjecture 2.3 of Goncalves, Monte Carmelo and Nakaoka, proved in the source only under an extra hypothesis. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $s\geq 2$ and $n\geq 2$ be integers. For positive integers $s,n$, let $M_s(n)$ denote the set multipartite Ramsey number for $C_4$ versus the star $K_{1,n}$, namely the least $c$ such that every spanning subgraph $G$ of the complete balanced $s$-partite graph $K_{c\times s}$ contains a copy of $C_4$ or its complement contains a copy of $K_{1,n}$. **Incremental conjecture.** For any integers $s\geq 2$ and $n\geq 2$, 
$$
M_s(n+1)\leq M_s(n)+1.
$$
 The preceding proposition proves this bound under an additional numerical hypothesis; the conjecture asserts that the hypothesis can be removed.

## Summary of the result

For all s >= 2 and n >= 2, M_s(n+1) <= M_s(n) + 1, where M_s(n) is the least positive c such that every spanning subgraph G of the complete multipartite graph with c classes of s vertices either contains a 4-cycle or leaves some vertex with at least n non-neighbours in other classes (a star K_{1,n} in the complement relative to the host). This is Conjecture 2.3 of Goncalves, Monte Carmelo and Nakaoka, who proved the inequality only under an additional numerical hypothesis by keeping the original partition. The proof here proves the stronger step that the property at (n, c) implies the property at (n+1, c+1) by abandoning the partition: delete s suitable vertices and re-partition the rest into c independent s-sets, by a one-vertex swap forced by C4-freeness when s >= 3, and for s = 2 by a friendship-type lemma (two vertices with no common neighbour) with a perfect matching in the complement, plus explicit small cases. Lean defines the host graph, the property and the minimum literally, and proves that the minimum exists.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
