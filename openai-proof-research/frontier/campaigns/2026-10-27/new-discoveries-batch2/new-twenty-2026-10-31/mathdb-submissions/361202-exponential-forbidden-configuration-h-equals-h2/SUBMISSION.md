# MathDB 361202: The general equality conjecture for H(m,α) and H_2(m,α)

- Problem: https://mathdb.com/p/361202
- Source: Wallace Peaslee, Attila Sali and Jun Yan, “An intermediate case of exponential multivalued forbidden matrix configuration”, arXiv:2312.11446 (2023), Conjecture 6.3. https://arxiv.org/abs/2312.11446
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `PSY.psy_conj_6_3`, `PSY.H_eq_H₂`, `PSY.recursive_dominates`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Wording: say 'kernel-checked proof of H(m, α) = H₂(m, α)', not 'of Conjecture 6.3': the 'in particular' limit follows from the equality via the source's Theorem 6.2, which the source states without a printed proof for α > 2 (for α = 2 it is the source's proved Theorem 1.9). The conjecture is also a problem in the public ReuF2F benchmark (cmu-l3/reuF2F, released 2026-10-16), whose Lean statement includes the limit clauses; per-problem results there are not public. Sibling MathDB 361201 (α = 2, Conjecture 1.10) is a special case and is not counted separately. Cross-model reviewer: not routine 0.65. The Lean was written by a Claude Opus 5.5 lane from a GPT-6.1 Sol proof; the final check was by a separate Opus lane (same model family as the packager) because GPT-6.1 Sol hit its usage limit; a Sol re-check after 2026-11-26 is advisable.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Peaslee, Sali and Yan's conjecture (arXiv:2312.11446, Conjecture 6.3) that H(m, α) = H₂(m, α) for all m ≥ 3 and α ≥ 2, in fact for every α > 1: every triple-choice multigraph is dominated by a 2-recursive one, by a normalized block-merging argument. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $H(m,\alpha)$ and $H_2(m,\alpha)$ be the quantities considered in the paper, with $m\geq 3$ and $\alpha\geq 2$, and define $\lambda(\alpha)=\sum_{j=1}^{\infty}\frac{2^{j-1}}{\alpha^{2^j}}$. **General equality conjecture.** $H(m,\alpha)=H_{2}(m,\alpha)$ for all $m\geq 3$ and $\alpha\geq 2$. In particular, $\lim_{m\to\infty}\frac{2H(m,\alpha)}{m\alpha^m}=\lim_{m\to\infty}\frac{2H_{2}(m,\alpha)}{m\alpha^m}=\lambda(\alpha)$.

## Summary of the result

H(m, α) = H₂(m, α) for every m ≥ 3, and in fact for every α > 1: every triple-choice multigraph is matched or beaten in weight by a 2-recursive one. The source's edge-swap lemma gives only a closed vertex pair, and its Section 6 suggests combining closed sets without carrying it out. The proof normalizes cross-block edge weights by (α^{|A|}−1)(α^{|B|}−1) to force a closed pair of blocks, then uses size-weighted cloning and the convexity of α^x to homogenize the union without losing weight, iterating from singleton blocks. Lean defines triple-choice multigraphs, the weight, 2-recursiveness (Definition 1.3) and H, H₂ as maxima over nonempty finite sets, and checks small values (H(3,2) = 4, H(4,2) = 12 by exhausting all 81 choices, H₂(5,2) = 30, H₂(6,2) = 73) and that a non-2-recursive choice exists. The 'in particular' limit follows from the equality and the source's Theorem 6.2, which Lean does not formalize.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
