# MathDB 358270: The strict lower-bound conjecture for the robust clique covering number

- Problem: https://mathdb.com/p/358270
- Source: Gábor Bacsó, Balázs Patkós, Zsolt Tuza and Máté Vizer, “The robust chromatic number of graphs”, arXiv:2305.01923 (2023). (https://arxiv.org/abs/2305.01923)
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `RobustCover.conjecture1`, `RobustCover.mathdb_358270`, `RobustCover.robust_theta_strict`, `RobustCover.robust_theta_required_strict`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Close call on significance (a few-line variant of the source technique; user may overrule). The journal version of the source is unread (publisher bot challenge).
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. For every finite simple graph G, the robust clique covering number theta_1(G), defined as the maximum over 1-selections (each vertex selects one incident edge) of the clique covering number after deleting the selected edges, equals the clique covering number theta(G) exactly when G has no edges. This is Conjecture 1 of the source; no isolate-free hypothesis is needed. The proof gives an explicit 1-selection that forces one more clique, adapting the source authors' own technique. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $G$ be an isolate-free graph. Write $\theta(G)$ for its clique covering number and $\theta_1(G)$ for the corresponding robustness parameter, so that the general lower bound is $\theta_1(G)\geq\theta(G)$. **Strict lower-bound conjecture.** The inequality is strict unless $G$ is edgeless; equivalently, equality can occur only for edgeless graphs. This conjecture asks for a characterization of the equality case in the lower bound for the robust clique covering number. Its status is not established in the supplied source.

## Summary of the result

For every finite simple graph G, the robust clique covering number theta_1(G) (the maximum, over 1-selections in which each vertex selects one incident edge, of the clique covering number after deleting the selected edges) equals the clique covering number theta(G) if and only if G has no edges. This is Conjecture 1 of the source, proved without the isolate-free hypothesis of the MathDB record. The argument modifies the proofs of Proposition 7 and Theorem 6 of the source by an explicit 1-selection. Significance is modest: a short argument on a question the source authors left open.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
