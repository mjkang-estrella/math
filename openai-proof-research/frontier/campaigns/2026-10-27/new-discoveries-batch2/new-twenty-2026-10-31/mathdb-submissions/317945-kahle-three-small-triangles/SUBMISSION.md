# MathDB 317945: The three-small-triangles conjecture for five points

- Problem: https://mathdb.com/p/317945
- Source: Matthew Kahle, “Points in a triangle forcing small triangles”, arXiv:0811.2449 (2008). (https://arxiv.org/abs/0811.2449), Conjecture 3.1
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `kahle_conj_3_1`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Degenerate triples are counted as small, the convention forced by the source's use of Soifer's one-triangle theorem. Soifer's book chapter on the problem (Springer) was not read; it is understood to reprint the 2008 material. Bounded literature search only.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Any five points in a closed triangle of unit area determine at least three triangles of area at most 1/4 (unordered triples; degenerate triples count as area 0; the threshold is inclusive). This is Conjecture 3.1 of Kahle, arXiv:0811.2449; the number three is sharp. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Call a triangle **small** if its area is at most $1/4$. Given five points in a triangle of unit area, consider the triangles determined by triples of the five points. **Three-small-triangles conjecture.** The five points determine at least three small triangles.

The claim would strengthen the preceding result, which guarantees only one small triangle. The source notes that three cannot be replaced by four for the displayed configuration; if true, the conjecture would imply corresponding lower bounds for larger point sets by averaging.

## Summary of the result

For any triangle of area 1 in the plane and any five points of the closed triangle (not necessarily distinct), at least three of the ten unordered triples of the points span a triangle of area at most 1/4, where degenerate triples count with area 0. This is Kahle's three-small-triangles conjecture; three cannot be replaced by four. The proof is a case analysis on the midpoint subdivision with a determinant identity; the reduction from an arbitrary triangle to a standard one is proved in Lean.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
