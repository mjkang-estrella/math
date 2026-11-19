# MathDB 366949: Lexicographic quasi-idempotent Schur duality for polynomial quantum wreath products

- Problem: https://mathdb.com/p/366949
- Source: Chun-Ju Lai and Alexandre Minets, “Schurification of polynomial quantum wreath products”, arXiv:2502.02108 (2026). (https://arxiv.org/abs/2502.02108)
- Outcome: **REFUTED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoint `PolySkew.MathDB366949_counterexample`; axioms limited to propext, Classical.choice, Quot.sound; independently extracted and replayed from `LEAN-SOURCE-APPENDIX.md`.
- Written proof: `PAPER.md` (independently reviewed, no theorem-affecting gaps).
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Lai-Minets Part III has no authenticated standalone body; Cambridge final unread.
- Produced with AI assistance (GPT-6.2 Sol and Claude Opus 5.5 investigators, independent AI review); not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: lexicographic Schur duality for polynomial quantum wreath products, the equality between the intersection algebra and the endomorphism algebra asserted by Lai-Minets Conjecture 6.12 without the additional hypothesis. Over the rationals, a five-dimensional coefficient algebra and d = 3 give a proper inclusion; the obstruction is a block map annihilating the cyclic generator's right annihilator while escaping its principal left ideal. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Assume that $B\wr \cH_d$ is a polynomial quantum wreath product satisfying conditions 
$$
and
$$
, and write $\bfH_d=B\wr \cH_d$. For each composition $\lambda\vDash d$, let $K_\lambda$ be defined by 
$$
with the product taken in lexicographic order. Define the right $\bfH_d$-module
$$

\bfC^\cT=\bigoplus_{\lambda}K_\lambda\bfH_d.

$$
Let
$$

\overline{\bfS}^\cT_d=\bigoplus_{\lambda,\mu}\overline{\bfS}^\cT_{\lambda,\mu},\qquad \overline{\bfS}^\cT_{\lambda,\mu}=K_\lambda\bfH_d\cap\bfH_dK_\mu,

$$
with multiplication $(xK_\mu)\cdot(K_\mu y)=xK_\mu y$ for $xK_\mu\in\overline{\bfS}^\cT_{\lambda,\mu}$ and $K_\mu y\in\overline{\bfS}^\cT_{\mu,\nu}$. **Lexicographic quasi-idempotent Schur duality conjecture.** The statement of Theorem
$$
 holds for this construction. This proposes that the strong double-centralizer property extends when only conditions 
$$
and
$$
 are imposed, despite the failure of the convolution-algebra approach without centrality. The source gives no resolution of this conjecture.

## Summary of the result

SUBSTANTIVE_BOUNDED: rank-three fixed-pair strict double annihilator lifted to the prescribed polynomial endomorphism block; no public match or routine specialization found.

The complete proof is in `PAPER.md`; the complete Lean source is in `LEAN-SOURCE-APPENDIX.md`.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
