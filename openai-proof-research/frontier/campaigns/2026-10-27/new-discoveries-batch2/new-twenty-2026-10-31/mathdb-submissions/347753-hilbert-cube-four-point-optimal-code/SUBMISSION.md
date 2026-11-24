# MathDB 347753: Four-point optimal-code conjecture for the Hilbert cube

- Problem: https://mathdb.com/p/347753
- Source: Emily J. King, Dustin G. Mixon, Hans Parshall and Chris Wells, Uniquely optimal codes of low complexity are symmetric, arXiv:2008.12871, Conjecture 27 (journal version: Conjecture 4.21, doi 10.56994/JXM.002.001.004). (https://arxiv.org/abs/2008.12871)
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `HilbertCode.conj27`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Bounded literature search only. The proof is one page of weighted averaging once the right weights and threshold are found, so a specialist could call it short (cross-model confidence: not routine 0.6, the lowest accepted in this list; correct 0.97; Lean statement equals the printed conjecture 0.97). The theorem is conditional on N as the conjecture is; admissible sets N exist by the source's Lemma 28, which is not formalized. The source notes that optimal codes of this kind are not unique.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. The four-point configuration printed in Conjecture 27 of King, Mixon, Parshall and Wells (arXiv:2008.12871) is an optimal code of size 4 in the Hilbert cube for every admissible index set N. The source proves the three-point case only. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $H$ be the Hilbert cube, with standard basis vectors $e_k$, and set

$$
\alpha:=\frac{\sqrt{2}\pi}{3}.
$$

Choose $N\subseteq\mathbb{N}$ such that

$$
\sum_{k\in N}\frac{1}{k^2}=\alpha-1,
$$

and define

$$
s:=\sum_{k=2}^\infty\frac{1}{k}e_k,\qquad t:=\sum_{k\in N}\frac{1}{k}e_k.
$$

**Hilbert-cube four-point conjecture.** The set

$$
\left\{0,\left(1-\frac{1}{2}\alpha\right)e_1+s,e_1+t,\frac{1}{2}\alpha e_1+s-t\right\}
$$

is an optimal code in the Hilbert cube. Numerical experiments on truncations motivate this prediction; the supplied text later confirms that such choices of $N$ exist but notes that the resulting codes are not unique.

## Summary of the result

For every set N of indices with the sum of 1/k^2 over N equal to sqrt(2) pi / 3 - 1, the four printed points form an optimal code of size 4 in the Hilbert cube: the set has four points, lies in the cube, and every four-point subset of the cube has two distinct points at distance no larger than the smallest distance of the printed set. This is Conjecture 27 of King, Mixon, Parshall and Wells, who proved the three-point case and left four points open. The proof sorts the four points by first coordinate, pushes the extreme ones to the faces, and splits into two cases at the threshold 1 - alpha/2: either one pair is already close, or a weighted sum of five squared distances with weights 1, 1, 2, 1, 1 is bounded by convexity at the corners of each coordinate box. Lean states the cube inside Mathlib's l^2 space with its own distance and quantifies over every four-element subset.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
