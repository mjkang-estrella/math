# MathDB 358162: Vanishing bounds for Romik's sequence v(n) modulo odd prime powers

- Problem: https://mathdb.com/p/358162
- Source: Christian Krattenthaler and Thomas W. Müller, “The congruence properties of Romik's sequence of Taylor coefficients of Jacobi's theta function θ_3”, arXiv:2304.11471 (v4, 2024), Conjecture 44 (the second conjecture). https://arxiv.org/abs/2304.11471
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `romik_conj44_odd`, `romik_conj44_even_exact`, `romik_conj44_even_lower`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Wording: the result proves the odd clause and classifies the even-clause exceptions exactly; the even clause says only 'with very few exceptions', so the exact classification is taken as its resolution (cross-model reviewer and final checker agree); the two unlisted exceptions are not counted as separate findings. Across all primes there are infinitely many exceptions (at least (p−1)/2 per prime). In arXiv v1 the conjecture was Conjecture 41 with the single exception (7,8). Cross-model reviewer: not routine 0.70. The Lean was written by a Claude Opus 5.5 lane from a GPT-6.1 Sol proof; the final check was by a separate Opus lane (same model family as the packager) because GPT-6.1 Sol hit its usage limit; a Sol re-check after 2026-11-26 is advisable. One Lean declaration raises maxHeartbeats.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved the odd clause of Krattenthaler and Müller's second conjecture on Romik's sequence (arXiv:2304.11471, Conjecture 44): p^e | v(n) for n ≥ (ep+2)(p+1)/4 when p ≡ 3 (mod 4) and e is odd; and classified every exception of the even clause exactly (finitely many for each p; the source's list of four misses (3,4) and (11,12)). The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $p$ be a prime with $p\equiv3\pmod4$, let $e\ge1$, and let $(v(n))_{n\ge0}$ be the sequence defined in the paper. **The second conjecture.** If $e$ is odd, then $v(n)\equiv0\pmod{p^e}$ for $n\ge\frac{(ep+2)(p+1)}{4}$. If $e$ is even, then $v(n)\equiv0\pmod{p^e}$ for $n\ge\left\lceil\frac{ep^2}{4}\right\rceil$, with very few exceptions. Based on data with $n\le1500$, the listed exceptions are $(p,e)=(7,8),(7,24),(7,40),(11,36)$, whose correct lower bounds are respectively $102,298,494,1095$.

## Summary of the result

The odd clause holds exactly as printed: for every prime p ≡ 3 (mod 4) and odd e, p^e divides v(n) for n ≥ (ep+2)(p+1)/4. For even e and n ≥ ⌈ep²/4⌉, the exceptions are classified exactly: p^e fails to divide v(n) if and only if e = (p+1)(2j+1) with 0 ≤ j < (p−1)/2 and 4n = ep² + (p+1) + 4r with 4r < p+1 and an explicit coefficient (r-th coefficient of a fixed polynomial over F_p) nonzero; at every exception v(n) misses by exactly one factor of p. The classification reproduces the source's four listed exceptions and corrected bounds, and shows the list is incomplete even within its own range (n ≤ 1500): (p,e) = (3,4) at n = 10 and (11,12) at n = 366–368. The source's own Theorem 17 is a factor of two weaker. The proof bounds the p-adic valuation of a square-root series within one factor of p, and supplies the last factor (odd e) or the exact failure set (even e) from a digit-level residue formula; the Lean proof obtains the residues mod p as coefficients of an explicit square root in characteristic p built from Frobenius. Lean defines v(n) by the source's recurrence (2.6) over ℚ, proves integrality, and checks the source's eleven printed values and its (7,8) data point.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
