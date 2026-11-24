# MathDB 375588: Half twists on two overlapping intervals define homomorphisms from dihedral Artin monoids to the positive braid monoid (Berenstein–Greenstein–Li Conjecture 6.35)

- Problem: https://mathdb.com/p/375588
- Source: Arkady Berenstein, Jacob Greenstein and Jian-Rong Li, “Artin monoids, their homomorphisms and twins”, arXiv:2606.26776 (2026), Conjecture 6.35; the same statement is Conjecture 5.85 of their arXiv:2405.18821v5. https://arxiv.org/abs/2606.26776
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `BGL.conj_6_35_monoid`, `BGL.conj_6_35_monoid_hom`, `BGL.conj_6_35_group`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Lean proves the relation and constructs the homomorphism for explicit triangular positive words. That those words are the source's positive lifts of the longest elements w₀ of the two parabolic subgroups is a written step: the words have the right number of letters in every rank and the right permutation (Lean checks the letter count in every rank and the reversal permutation at n = 4, 6, 7; the general statement is the standard inversion count in type A together with the Matsumoto–Tits theorem that all reduced words of an element give the same positive braid). The first version of the Lean packet proved the statement only in the braid group and assumed Garside's embedding for the monoid; the GPT-6.2 Sol cross-model review failed it for that, and stage 2 removed the assumption. MathDB 363298 is the same conjecture (from the authors' 2024 paper) and counts once with this one. The source proves two subfamilies (N = 3 and N = 4). No full prior resolution was found; V. Sury's 2026 thesis was screened by abstract only. Proof, first (same-model) review and Lean stage 1 are by Claude Opus 5.5; the cross-model review (mathematics correct, not routine 0.60), Lean stage 2 and the final check (a separate lane) are by GPT-6.2 Sol, so the final check is by the same model family as the stage-2 packager.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Berenstein, Greenstein and Li (arXiv:2606.26776, Conjecture 6.35; also arXiv:2405.18821) conjectured that in three numerical cases the half twists on the strand intervals [1,a] and [b,n−1] satisfy the dihedral braid relation of length N in the positive braid monoid, giving homomorphisms Br⁺(I₂(N)) → Br⁺_n. All three cases are proved for every n: two by rotation and overlap identities for half twists, the third (N = 6) by cabling a four-strand identity. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $1\le b\le a<n-1$ and $a>1$. For the type-$A$ braid monoid, write $w_0^{[r,s]}$ for the longest element of the parabolic subgroup on the interval $[r,s]$.

**Interval-family homomorphism conjecture.** The assignments

$$
\widehat{T}_1\mapsto T_{w_0^{[1,a]}},\qquad \widehat{T}_2\mapsto T_{w_0^{[b,n-1]}}
$$

define a homomorphism $\operatorname{Br}^+(I_2(N))\to\operatorname{Br}^+_n$ if one of the following holds:

$$
N=\frac{2n}{n+b-a-2}\in2\mathbb Z_{>0};
$$

$$
a+b=n\quad\text{and}\quad N=\frac{n}{b-1}\in1+2\mathbb Z_{>0};
$$

$$
a+1=2(b-1),\quad a+b<n,\quad\text{and}\quad N=6.
$$

The paper presents these as a conjectural infinite family of non-disjoint standard homomorphisms and reports verification for $n\le15$.

## Summary of the result

The conjecture holds in all three cases and for every n: the two half twists (positive lifts of the longest elements on the intervals [1,a] and [b,n−1]) satisfy the braid relation of length N in the positive braid monoid, so they define a monoid homomorphism from the dihedral Artin monoid Br⁺(I₂(N)). Cases I and II follow from a periodic-braid identity: rotation and overlap identities for half twists, proved by positive rewriting. Case III (N = 6) comes from a seven-move identity on four strands, transported to all sizes by cabling with strands of unequal width. The source proves the subfamilies N = 3 (of case II) and N = 4, b ≥ 2 (of case I) and reports computer verification for n ≤ 15. Lean works in the presented positive monoid on σ₁, …, σ_{n−1} with the braid and commutation relations, defines the half twists as explicit triangular positive words, and proves both the alternating relation and the existence of the homomorphism with no premise beyond the conjecture's hypotheses; an earlier group-level proof is kept.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
