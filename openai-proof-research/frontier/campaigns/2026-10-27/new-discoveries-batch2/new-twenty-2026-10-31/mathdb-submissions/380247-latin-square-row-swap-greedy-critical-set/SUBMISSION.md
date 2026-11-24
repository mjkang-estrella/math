# MathDB 380247: Greedy critical sets of the abelian 2-group Latin square after swapping two rows less than three apart are 2-critical, strong and complete top down (Hämäläinen's Conjecture 6.1)

- Problem: https://mathdb.com/p/380247
- Source: Carlo Hamalainen, “New 2–critical sets in the abelian 2–group”, arXiv:math/0612338 (2006; J. Combin. Math. Combin. Comput. 61, 2007), Conjecture 6.1. https://arxiv.org/abs/math/0612338
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `Rowswap.conj_6_1`, `Rowswap.printed_order_counterexample`, `Rowswap.Ls_eq_recursiveSquare`, `Rowswap.printedOrder_eq_formula`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The result is for the bottom-to-top greedy order that the source's prose, proofs and tables use; the source's displayed formula for that order is a misprint (it runs top to bottom), and under it the top-down clause fails at order four for the swap (0,1), a case of the source's own Theorem 5.1; Lean proves that failure. All 18 tables of the compiled paper and 90 further order-32 tables in the arXiv TeX source match the bottom-to-top order and none matches the formula. 'Strong' and 'completes top down' are formalized in their strongest natural reading (one forced cell at a time, rows in order). The aligned case was already proved by the author; what is new is every larger order for the swaps crossing a block boundary, chiefly the two distance-two families, and one family of new cases is easy. Hamalainen's 2007 PhD thesis could not be read (the repository refuses automated access; reviewer's probability that it settles the conjecture: about 0.07). A modest result in a small literature (two citing works). All work is by AI and no human has checked it: the proof, the Lean code and the paper are by GPT-6.2 Sol lanes; the adversarial review before Lean (not routine 0.72) and the final check (0.66) are by two separate Claude Opus 5.5 lanes. The final-check lane ran one read-only git command on a local clone against the rules; nothing was changed.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved, for the greedy order the source describes in words. Hamalainen (arXiv:math/0612338, Conjecture 6.1) conjectured that after swapping two rows less than three apart in the Latin square of the elementary abelian 2-group of order 2^s, the greedy critical set is 2-critical, strong and completes top down; he proved the aligned case and checked the rest by computer through order 32. Explicit binary masks give the greedy set for every order, with a private intercalate for each clue and an acyclic forcing order in each row. The source's displayed formula for the greedy order is a misprint: under it the statement already fails at order four. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $L_s$ be the latin square of order $n=2^s$, and let $\alpha_{k,k'}$ be the row isotopism that interchanges rows $k$ and $k'$ and fixes every other row. Suppose that

$$
\left|k-k'\right|<3.
$$

**Strengthened 2-criticality conjecture.** The set $\operatorname{gcs}(\alpha_{k,k'}L_s)$ is 2-critical and strong, and completes top down to $\alpha_{k,k'}L_s$.

The theorem preceding this conjecture proves the claim under the additional hypothesis that $k$ and $k'$ lie among four consecutive indices beginning at a multiple of $4$. The authors expect that this stronger version remains true when that additional condition is weakened, but no resolution is given here.

## Summary of the result

The conjecture holds for every order 2^s and every pair of rows less than three apart, for the greedy order that the source describes in words and uses throughout (bottom row first, right to left). For each such swap the greedy critical set is given by explicit blank-cell masks written in binary across block boundaries; each clue is the lexicographically least cell of a private intercalate, which gives 2-criticality, and in each row the blanks are forced one at a time along an acyclic forcing graph, which gives strong completion and top-down completion. The source proved the case where both rows lie in an aligned block of four (its Theorem 5.1) and checked the rest by computer through order 32; the new cases are the swaps that cross a block boundary, of which the odd adjacent ones are easy and the two distance-two families carry the substance. Lean defines the square by bitwise exclusive or and proves it equal to the source's recursive square, defines the greedy algorithm with its uniqueness test over all Latin squares of the order, 2-criticality by private intercalates, strong completion and top-down completion by forced cells, and proves the three properties for all s and all such swaps. Lean also proves that with the source's displayed formula for the greedy order, which runs the other way, top-down completion fails at order four for the swap of rows 0 and 1.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
