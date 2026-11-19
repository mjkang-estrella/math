# MathDB 369952: Failure of the matroid matching property in odd-dimensional rigidity matroids

- Problem: https://mathdb.com/p/369952
- Source: John Hewetson, Bill Jackson, Anthony Nixon and Ben Smith, “k-fold circuits and coning in rigidity matroids”, arXiv:2508.18838 (2026). (https://arxiv.org/abs/2508.18838)
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoint `literal endpoint per CROSSWALK.md (independent extracted replay PASS, 41 modules)`; axioms limited to propext, Classical.choice, Quot.sound; independently extracted and replayed from `LEAN-SOURCE-APPENDIX.md`.
- Written proof: `PAPER.md` (independently reviewed, no theorem-affecting gaps).
- Novelty: bounded literature and registry review only; no worldwide-priority claim. User may overrule. Dress-Lovasz Springer body unread.
- Produced with AI assistance (GPT-6.2 Sol and Claude Opus 5.5 investigators, independent AI review); not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: the matroid matching property fails in odd-dimensional generic rigidity matroids, as conjectured in the source. In every odd dimension d >= 5 there is a pair family of edges of a complete graph whose largest rigidity-matroid matching has size h-2 while the Dress-Lovasz lower bound gives h-1; the construction and both extrema also hold for every real placement with algebraically independent coordinates. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

For integers $k\geq 2$ and sufficiently large $n$, consider the rigidity matroid ${\mathcal R}_{2k+1}(K_n)$ of the complete graph $K_n$ in dimension $2k+1$. **The matroid matching conjecture.** The matroid ${\mathcal R}_{2k+1}(K_n)$ does not have the matroid matching property for all $k\geq 2$ and sufficiently large $n$. The preceding proof establishes the corresponding even-dimensional result, while the odd-dimensional case is suspected to fail in this way for dimensions at least five and large complete graphs.

## Summary of the result

MODEST_BOUNDED (close call): explicit pair family in odd dimension d>=5 with maximum matching h-2 against Dress-Lovasz minimum h-1; a reviewer derived an unpublished alternate coning route, which weakens the significance but is not prior art.

The complete proof is in `PAPER.md`; the complete Lean source is in `LEAN-SOURCE-APPENDIX.md`.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
