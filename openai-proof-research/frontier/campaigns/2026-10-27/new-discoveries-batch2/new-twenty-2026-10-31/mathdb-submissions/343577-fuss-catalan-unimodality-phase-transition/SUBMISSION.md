# MathDB 343577: Phase-transition conjecture for unimodality of Fuss–Catalan distributions

- Problem: https://mathdb.com/p/343577
- Source: Wojciech Mlotkowski, Noriyoshi Sakuma and Yuki Ueda, Free self-decomposability and unimodality of the Fuss-Catalan distributions, arXiv:1908.07887 (J. Stat. Phys. 178 (2020) 1055-1075). (https://arxiv.org/abs/1908.07887)
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `FussCatalan.density_measure_phase_transition`, `FussCatalan.mu_supported`, `FussCatalan.mu_ne_zero`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The Lean statement is tied to the source's object by a cited published theorem, not by Lean: Lean classifies the measure with the explicit density; its identification with the moment-defined mu(p, r), normalization included, is the source's Proposition 1.1 (Forrester and Liu 2015, Proposition 2.1). Two reviewers confirmed numerically that this density has mass one and the first Raney moments. Bounded literature search only. Cross-model confidence: correct 0.97, not public 0.85, not routine 0.65, Lean statement equals the printed conjecture modulo the cited proposition 0.95. The proof is short once the monotonicity in r is seen. The author packet's own report calls it PARTIAL relative to an earlier endpoint that included normalization.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. For every p > 1 there is r0 in (p - 1, p) such that the Fuss-Catalan distribution mu(p, r), 0 < r <= p, is unimodal exactly when r = p or r <= r0. This is the phase-transition conjecture of Mlotkowski, Sakuma and Ueda (arXiv:1908.07887). The Lean proof is for the measure with the explicit density of the source's Proposition 1.1; that this is mu(p, r) is that published proposition, cited. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $p>1$ and let $\mu(p,r)$ denote the Fuss–Catalan distribution with parameters $p$ and $r$. **Phase-transition conjecture.** For every $p>1$ there exists $r_{0}(p)$ satisfying

$$
p-1<r_{0}(p)<p,
$$

such that $\mu(p,r)$ is unimodal if and only if either $r=p$ or $0<r\leqslant r_{0}(p)$. This conjecture is suggested by the results in the preceding sections and by numerical experiments; the general phase transition remains open.

## Summary of the result

For every p > 1 there is r0 with p - 1 < r0 < p such that, for 0 < r <= p, the Fuss-Catalan distribution mu(p, r) is unimodal if and only if r = p or r <= r0. Lean proves this for the measure with the explicit density of the source's Proposition 1.1, formula (2) (due to Forrester and Liu), with unimodality in the source's sense (an atom plus a density nondecreasing before and nonincreasing after the mode). That this measure is the moment-defined distribution mu(p, r), total mass one included, is the source's published Proposition 1.1, cited and not checked in Lean. The proof shows that the logarithmic derivative of the density is strictly decreasing in r, so the unimodal parameters form an interval, and locates its endpoint strictly between p - 1 and p.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
