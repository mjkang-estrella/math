# MathDB 324112: The three conjectural sporadics in the entropic order on a parabolic quotient of S6

- Problem: https://mathdb.com/p/324112
- Source: Gary McConnell, “An entropic partial order on a parabolic quotient of S6”, arXiv:1209.2674 (2012), Conjecture 19. https://arxiv.org/abs/1209.2674
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `McConnell.mcconnell_conj19`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Modest result: about three pages of elementary calculus on a single explicit inequality from a 2012 arXiv preprint with one citing paper; the cross-model reviewer puts 0.60 on a specialist calling it not routine. The source's Definition 4 states the direction of the order once the wrong way round; the convention paragraph and the falsity of the reverse fix the direction used. ProbXiv (HTTP 402) and OpenAlex (429 for one lane) were not fully checked. No second cross-model lane read the finished Lean: root compared the final theorem and every definition with the endpoint the Claude Opus reviewer had written (identical), and the GPT-6.1 Sol final check derived the four arrays from the source independently and spot-checked 240 points.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. McConnell's three sporadic relations 37, 43, 49 ▷ 11 in the entropic order on a parabolic quotient of S6 (arXiv:1209.2674, Conjecture 19) hold on the whole closed domain: the mutual information of each of the three arrays is at most that of array 11. Convexity-only arguments provably fail; the proof is a three-page reduction to faces with a weighted gradient bound on the hardest face. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

For a probability vector $a\geq b\geq c\geq d\geq e\geq f\geq 0$ placed in a $2\times 3$ array, let $I$ be the classical mutual information between the row and the column of the array, and write $\sigma\rhd\sigma'$ when $I(P^{\sigma})\leq I(P^{\sigma'})$ for every such vector. **Three sporadic entropic-order conjectures.** $\mathbf{37}\rhd\mathbf{11}$, $\mathbf{43}\rhd\mathbf{11}$ and $\mathbf{49}\rhd\mathbf{11}$, where $\mathbf{11}=\begin{pmatrix}a&b&d\\f&c&e\end{pmatrix}$, $\mathbf{37}=\begin{pmatrix}a&c&f\\b&d&e\end{pmatrix}$, $\mathbf{43}=\begin{pmatrix}a&d&e\\b&c&f\end{pmatrix}$, $\mathbf{49}=\begin{pmatrix}a&d&f\\b&c&e\end{pmatrix}$.

## Summary of the result

All three relations hold on the whole closed ordered domain, ties and zero entries included. Arguments that use only convexity of x log x (majorization, Schur concavity, Karamata) cannot work, because the inequalities fail when x log x is replaced by x squared, as the source remarks, and the author wrote that these three relations do not yield to the identric-mean technique that proved the others. The proof reduces to a = b by the sign of the derivative in a, uses concavity along a direction that keeps the positive marginals fixed to reduce to five faces of the domain, treats each face by one-variable monotonicity, and on the hardest face uses a weighted gradient bound (log x >= 1 - 1/x with an explicit nonnegative polynomial) followed along the curves A/C^2 = constant. Lean states the mutual information with Mathlib's negMulLog, keeps the joint-entropy term, fixes the direction of the order, and writes the four arrays out explicitly.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
