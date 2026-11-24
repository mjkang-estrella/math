# MathDB 346681: Fixed-point product formula conjecture for evacuation of Kreweras words

- Problem: https://mathdb.com/p/346681
- Source: Sam Hopkins and Martin Rubey, “Promotion of Kreweras words”, Selecta Math. 28 (2022), arXiv:2005.14031, Conjecture 6.3. (https://arxiv.org/abs/2005.14031)
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `Kreweras.mathdb346681`, `Kreweras.origin_series`, `Kreweras.adjacent_series`, `Kreweras.T_coeff`, `Kreweras.T_square_coeff`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Bounded literature search only. The domino step is Stanley's and the slit-plane step is Bousquet-Melou's; the new part is the unfolding of the states into slit-plane walks (about two pages), so a specialist could regard the result as a careful combination of known tools (cross-model confidence: not routine 0.7, not public 0.85). The source's authors note that Stanley's q = -1 result applies and still leave the formula open; Gatzweiler and Krattenthaler (2025) prove only the positivity part of the neighbouring Conjecture 6.2.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. For every n >= 1 the number of Kreweras words of length 3n fixed by dual evacuation is the product formula of Hopkins and Rubey's Conjecture 6.3, and the number fixed by evacuation is the same for even n and 0 for odd n. The fixed points are put in bijection with lattice walks avoiding a half-line, which are counted by the slit-plane method (series T with T = 1 + 4t^3T^3). The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $n\geq 1$, and let $\operatorname{{Evac}}$ and $\operatorname{{Evac}}^{*}$ denote the two evacuation operations on Kreweras words of length $3n$. For a word $w$, consider the fixed-point conditions $\operatorname{{Evac}}^{*}(w)=w$ and $\operatorname{{Evac}}(w)=w$.

**Evacuation fixed-point conjecture.** For all $n\geq 1$, the number of Kreweras words of length $3n$ satisfying $\operatorname{{Evac}}^{*}(w)=w$ is

$$
\frac{3^{\lfloor n/2 \rfloor} 4^{\lceil n/2 \rceil} \prod_{j=1}^{\lfloor n/2 \rfloor}(3j-1) \prod_{j=1}^{\lceil n/2 \rceil}(3j-2) }{(n+1)!}.
$$

The number satisfying $\operatorname{{Evac}}(w)=w$ is the same when $n$ is even and is $0$ when $n$ is odd. These formulas provide product expressions for the evacuation fixed points, while their status beyond the conjecture is not established in the supplied text.

## Summary of the result

For every n >= 1, the number of Kreweras words of length 3n fixed by dual evacuation equals the product P(n) of Hopkins and Rubey's Conjecture 6.3, and the number fixed by evacuation equals P(n) for even n and 0 for odd n. The proof passes through Stanley's correspondence between evacuation-fixed linear extensions and domino chains of order ideals, then unfolds the reachable states, which fall into three parity sectors, into lattice walks with steps (1,1), (-1,0), (0,-1) that avoid a half-line (the new step), and counts those walks by Bousquet-Melou's slit-plane method: the walk series are T and X*T^2 with T = 1 + 4t^3T^3. Lean formalizes the words, the swap operators, evacuation and dual evacuation literally, with bridge theorems to the source's poset formulation, and proves the walk enumeration for this step set from scratch (61 modules).

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
