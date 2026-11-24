# MathDB 361017: Subtraction games with at most three moves and the extension property have preperiod 0 (Miklós–Post Conjecture 2)

- Problem: https://mathdb.com/p/361017
- Source: István Miklós and Logan Post, “Superpolynomial period lengths of the winning positions in the subtraction game”, arXiv:2312.02426 (2023); Int. J. Game Theory (2024), doi 10.1007/s00182-024-00911-5; Conjecture 2. https://arxiv.org/abs/2312.02426
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `Subtraction.conjecture2`, `Subtraction.conjecture2_k1`, `Subtraction.pure_of_period`, `Subtraction.lemmaK`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The scope is that of Conjecture 2: binary win/loss outcomes, arbitrary seeds, at most three positive moves, and the extension hypothesis (the k = 1 hypothesis suffices; for seeded games it can hold when the all-k hypothesis fails). The argument is short and elementary; the contribution is the three-translate lemma. The source's separate remark that two-move games are purely periodic for arbitrary seeds is false under its printed recurrence, and its {3,5,11} example gives preperiod 11, not 12, under its own definition; neither affects Conjecture 2. No public resolution was found; exact-id omega registry queries on 2026-11-23 were rate-limited (keyword issue and pull-request queries returned nothing). Proof, first (same-model) review and Lean are by Claude Opus 5.5; the cross-model review and final check are by GPT-6.2 Sol (not routine 0.64).
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Miklós and Post (arXiv:2312.02426, Conjecture 2) conjectured that a subtraction game with at most three moves whose move set is extended by p + x for every move x (p the period) has preperiod 0. The proof pulls the periodic tail backward with the authors' extension criterion and excludes extra early losing positions by an inclusion–exclusion lemma on three translates. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $A$ be a finite subtraction set with $|A|\leq 3$, let $S\in\{0,1\}^{\alpha}$ be a seed, and write $p=\operatorname{Per}(A,S)$. An integer of the form $kp+x$ is an **extension** of $A$ for every $k\in\mathbb{N}_+$ and $x\in A$ under the condition stated. **Preperiod-extension conjecture.** If $kp+x$ is an extension of $A$ for all $k\in\mathbb{N}_+$ and $x\in A$, then

$$
\operatorname{PrePer}(A,S)=0.
$$

The statement is the converse of the cited invariant-extension proposition for sets of size at most three. The source notes that it suffices to check $k=1$, and that the converse is not true for nonempty seeds in the unrestricted setting.

## Summary of the result

The conjecture holds: for a subtraction game with at most three moves and any seed, if p + x is an extension of the move set for every move x (p the period of the outcome sequence), then the outcome sequence is purely periodic. The source's extension criterion, applied at n + p, pulls the losing positions of the periodic tail backward into the start of the sequence; what remains is to exclude an extra early losing position. Such a position would force all of its forward neighbours to be winning in the periodic tail, and a new counting lemma (Lemma K: inclusion–exclusion on three translates of the set of losing residues, with matching singleton and pair counts and a pointwise triple inclusion) shows that this cannot happen when there are at most three moves. Lean proves the literal conjecture, the version with the hypothesis only for k = 1, a stronger pure-periodicity statement, and Lemma K; it also proves that the statement fails for four moves ({1,2,6,11}) and that Lemma K fails for {2,5,6,7}.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
