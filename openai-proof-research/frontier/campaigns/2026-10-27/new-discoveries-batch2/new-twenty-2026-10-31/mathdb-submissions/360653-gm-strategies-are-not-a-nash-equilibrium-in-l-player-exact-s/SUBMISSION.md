# MathDB 360653: GM strategies are not a Nash equilibrium in l-player exact slow NIM(n, n-1) for n, l >= 3: a refutation of Gurvich-Naumova Conjecture 1 (arXiv:2311.03257)

- Problem: https://mathdb.com/p/360653
- Source: Gurvich-Naumova arXiv:2311.03257v1 Conjecture 1 (credited record MathDB 360653); Gurvich-Naumova arXiv:2312.08382v1 Conjecture 1, Discrete Appl. Math. 358 (2024) 382-394 (MathDB 361128, duplicate statement, no separate credit)
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `SlowNim360653.conjecture1_false : ¬ SlowNim360653.Conjecture, where Conjecture := for all n >= 2, l >= 2, initial positions x : Fin n -> N and rational C exceeding the length of every play from x under every legal positional profile, the all-GM profile (minimal multiple of l kept, largest index; largest entry kept when no multiple exists) is a Nash equilibrium for the payoff -(C - L) to the loser (player L mod l) and (C - L)/(l - 1) to each other player against every legal positional unilateral deviation; witnessed at n = l = 3, x = (4,4,5), C = 7`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `manuscript.pdf`
- Lean source: `source.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: DAM 2024 version of record of the sibling paper unread; bounded citing-work coverage (OpenAlex; Crossref, Semantic Scholar and DBLP unavailable) trust_limits: Lean 4.34.1 core/Std and pinned mathlib trusted; leanchecker shares the installation not_claimed: minimality of (4,4,5) ((2,4,4) gives a smaller improvement); existence or classification of other equilibria; priority; publication; separate credit for 361128
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: Gurvich-Naumova Conjecture 1 on the l-player exact slow variant of the takeaway game NIM(n, n-1): for every n >= 3 and l >= 3, the GM strategies are not a Nash equilibrium. A computed certificate at the parameters (5,5,6) shows no completion of the no-multiple convention repairs the claim, while the two-player case remains the known positive theorem. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Conjecture 1 fails for every n >= 3 and l >= 3 (ordinary block-invariant proof; Lean certifies (4,4,5)); a computed certificate at (5,5,6) shows no completion of the no-multiple convention rescues it; l = 2 is the GMMV23 theorem

## Body (paste into the MathDB body field)

Use the written proof in this folder: manuscript.pdf. The complete Lean source is in source.zip.
