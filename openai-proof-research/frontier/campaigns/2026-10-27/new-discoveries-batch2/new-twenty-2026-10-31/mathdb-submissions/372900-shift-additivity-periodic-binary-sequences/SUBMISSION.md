# MathDB 372900: The shift conjecture for periodic binary sequences of high nonlinear complexity, in its full range c ≥ ⌈n/2⌉ (Yuan–Li–Zeng Conjecture 1)

- Problem: https://mathdb.com/p/372900
- Source: Qin Yuan, Chunlei Li and Xiangyong Zeng, “The structure and enumeration of periodic binary sequences with high nonlinear complexity”, arXiv:2602.01134 (2026); IEEE Trans. Inform. Theory 72(8) (2026) 6189–6203; Conjecture 1. https://arxiv.org/abs/2602.01134
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `RightShift.conjecture1`, `RightShift.conjecture1_struct`, `RightShift.conjecture1_add`, `RightShift.run_lemma`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The journal version (IEEE Trans. Inform. Theory 72(8) (2026) 6189–6203, doi 10.1109/TIT.2026.3695307) could not be read: the reviewer puts 0.12 on its settling Conjecture 1 and 0.03 on the related Liang–Zeng–Tang ISIT 2026 paper doing so (0.17 that some unread or missed public work settles it), so both should be checked by hand before any unqualified novelty claim; the only arXiv version leaves the conjecture open and says the authors' technique does not prove it. The Lean statement reads the source's Definition 3 with additivity parameter t ≥ 0 (the source says positive t but uses add = 0; both readings are covered). Proof, first (same-model) review and Lean are by Claude Opus 5.5; the cross-model review and final check are by GPT-6.2 Sol (two rounds; not routine 0.72).
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Yuan, Li and Zeng (arXiv:2602.01134, Conjecture 1) conjectured that if a shift R^b of a periodic binary sequence in their class B(n, c, n − c), c ≥ ⌈n/2⌉, lies in B(n, c, d₂) with a larger additivity parameter, then b = d₂; they proved it for c ≥ ⌈(2n−1)/3⌉ and said their technique stops there. A new lemma on the lengths of zero runs of the difference word proves it in the full range. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $n$ be a positive integer, let $c\geq \left\lceil\frac{n}{2}\right\rceil$, and let $d=n-c$. Let $\mathcal{B}(n,c,d)$ denote the specified class of binary sequences, let $R^b(\mathbf{s}_n)$ denote the $b$-fold shift of $\mathbf{s}_n$, and let $\operatorname{add}(\mathbf{s}_n)$ denote its additivity parameter. Suppose that $0<b<n$ and that, for some $d_2$, $R^b(\mathbf{s}_n)\in\mathcal{B}(n,c,d_2)$ with $\operatorname{add}(R^b(\mathbf{s}_n))>\operatorname{add}(\mathbf{s}_n)$. **Shift-additivity conjecture.** Then $b=d_2$. The conjecture would extend the statements of the cited proposition and corollary from $c\geq\left\lceil\frac{2n-1}{3}\right\rceil$ to $c\geq\left\lceil\frac{n}{2}\right\rceil$, allowing the same conclusions about the unique relevant shift and the nonlinear complexity of the associated periodic sequence; the source reports experimental evidence but says that the proposed technique does not prove it.

## Summary of the result

The conjecture holds in its full range c ≥ ⌈n/2⌉. The source's Lemma 7 and Corollary 1 give b = d₂ when the two spacings and the two additivity parameters satisfy an inequality, which covers c ≥ ⌈(2n−1)/3⌉, and the authors say that their technique does not reach further. The new tool is a Run Lemma about the multiset of lengths of zero runs of the cyclic difference word of a sequence in the class B(n, c, d): comparing these run lengths before and after the shift handles the overlap that the published argument leaves open, and a reflection argument on cyclic windows finishes the proof. Lean states the source's Definitions 2 and 3 and the shift R^b literally for sequences Fin n → Bool, includes the membership of the original sequence in B(n, c, n − c) that the MathDB paraphrase leaves implicit, proves that the additivity parameter exists and is unique on the class, and proves the conjecture; it also shows by an example that the strict inequality in the hypothesis is needed.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
