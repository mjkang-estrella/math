# MathDB 323535: Ilinca–Kahn conjectured bipartite matching entropy bound

- Problem: https://mathdb.com/p/323535
- Source: Liviu Ilinca and Jeff Kahn, “Asymptotics of the Upper Matching Conjecture”, arXiv:1205.4342 (2012). (https://arxiv.org/abs/1205.4342), Conjecture 3.1, equation (20)
- Outcome: **REFUTED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `ilinca_kahn_conj31_not`, `ilinca_kahn_conj31_false`, `ik_family_violation_base_two`, `ik_family_count`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The journal version of the source (JCTA 120, 2013) and journal versions of related papers are unread; the literature search was bounded.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Refuted. For every m >= 3 the bipartite graph K_{m,m+1} plus a disjoint edge, with parts of sizes m+1 and m+2 and no isolated vertices, has (m+1)! matchings saturating the smaller part, strictly more than the upper bound of Ilinca-Kahn Conjecture 3.1 (equation (20)). The proof uses convexity of log Gamma for m >= 4 and an exact integer certificate at m = 3. The special case with all left degrees equal and integral t, which the authors singled out, is not refuted and remains open. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $G$ be a bipartite graph on $X\cup Y$ with $|X|=\ell$ and $|Y|=M\geq \ell$. For each $x\in X$, let $d_x$ be its degree, and define

$$
\psi(d,t)=t^{-1}\bigl[\log d!-\log \Gamma(d-t+1)\bigr],
$$

where $\Gamma$ is the usual gamma function. Let $\Phi_\ell(G)$ denote the number of matchings of size $\ell$ in $G$.

**Ilinca–Kahn conjectured matching bound.** If, for each $x\in X$, $t_x=\ell d_x/M$, then

$$
\log\Phi_\ell(G)\leq \sum_{x\in X}\psi(d_x,t_x).
$$

This proposed inequality is a precise version of an earlier entropy bound discussed in the paper. The source proposes it as a conjecture and does not provide a proof or resolution.

## Summary of the result

For every m >= 3 the bipartite graph K_{m,m+1} together with a disjoint edge, with parts of sizes m+1 and m+2, has (m+1)! matchings saturating the smaller part, which strictly exceeds the bound of Ilinca-Kahn Conjecture 3.1; the natural-log gap is about 0.0253 at m = 3 and increases. The proof uses tangents to the convex function log Gamma for m >= 4 and an exact integer chord certificate for m = 3; within this family m = 1, 2 satisfy the bound. The special case the authors were most confident of (all left degrees equal with integral t) is not refuted and remains open.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
