# MathDB 362603: Linear-threshold conjecture for connected size Ramsey numbers of star matchings

- Problem: https://mathdb.com/p/362603
- Source: Fanghua Guo, Yanbo Zhang and Yunqing Zhang, “Matching-star size Ramsey numbers under connectivity constraint”, arXiv:2404.03175 (2024); journal version 2025, Conjecture 1.3. (https://arxiv.org/abs/2404.03175)
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `StarRamsey.mathdb_362603`, `StarRamsey.connectedRamsey_eq_five`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The constant 5 is not optimised. Bounded literature search only; the 2025 journal version still lists the conjecture as open. Two references the referee could not verify (arXiv:2606.04439, arXiv:2604.17356) were removed from the revised paper.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved with c = 5. For all positive n, p, m with m >= 5(n+p), the connected size Ramsey number r_c(nK_{1,p}, K_{1,m}) equals n(m+p)-1. This is the linear-threshold conjecture of Guo, Zhang and Zhang (arXiv:2404.03175), who proved the formula under a quadratic threshold. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $nK_{1,p}$ be the disjoint union of $n$ copies of the star $K_{1,p}$, and let $K_{1,m}$ be the star with $m$ edges. The connected size Ramsey number $\hat r_c(G_1,G_2)$ is the minimum number of edges in a connected graph $G$ such that $G\to (G_1,G_2)$. **Linear-threshold conjecture.** There exists a positive constant $c$ such that for all positive integers $m$, $n$, and $p$ with $m\geq c(n+p)$, we have

$$
\hat r_c(nK_{1,p},K_{1,m})=n(m+p)-1.
$$

The conjecture proposes that the exact value established in the paper for the stronger condition $m\geq (n^2+2pn+n-3)/2$ remains valid once $m$ is merely linear in $n+p$.

## Summary of the result

For all positive integers n, p, m with m >= 5(n+p), the connected size Ramsey number of n vertex-disjoint stars K_{1,p} (red) against a star K_{1,m} (blue) equals n(m+p)-1: the minimum number of edges of a finite connected simple graph every red/blue edge colouring of which contains a red nK_{1,p} or a blue K_{1,m}. This proves the linear-threshold conjecture of Guo, Zhang and Zhang with c = 5; the source had the formula only for m >= (n^2+2pn+n-3)/2. Lean proves both the upper bound by construction and the lower bound for every connected graph with fewer edges. The constant 5 is not optimised; no constant c <= 2/3 can work (referee's computation at (n,p,m) = (2,1,2)).

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
