# MathDB 335354: Arithmetic conjectures for the normalized denominators of the Fabius function

- Problem: https://mathdb.com/p/335354
- Source: Juan Arias de Reyna, “Arithmetic of the Fabius function”, arXiv:1702.06487 (2017). https://arxiv.org/abs/1702.06487
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `FabiusProofLane.arias_de_reyna_conjecture_16`, `FabiusProofLane.mathdb335354_arithmetic`, `Fabius.existsUnique_fabius`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. About three quarters of the Lean source is third-party: 6,173 lines of the public ProveIt Fabius library, its 809-line existence proof and its nine-line statement of the conjecture (repository VladimirReshetnikov/ProveIt, MIT No Attribution licence, commit 39d36e12), unchanged and identified in the packet; about 2,400 lines, the proof of the conjecture itself, are new. Say so wherever the result is described. That project is active in the same area and listed the conjecture as open on 2026-11-20 (992 Fabius Lean files checked); it could publish its own proof at any time. Sebbar's 2025 article in the Monthly is unread (publisher refusal; expository; risk put at 2 to 3 percent). The packet's runner does not treat warnings as errors (the unchanged sources have style warnings); root confirmed directly that the endpoints depend only on the three allowed axioms and that the one occurrence of the word 'sorry' is inside a comment. Cross-model confidence: correct 0.95, novelty 0.88, first tier 0.65. The cross-model reviewer read the 34 proof modules before existence was added; the final theorem with existence was checked by the GPT-6.1 Sol final check and replayed by root.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. All clauses of Conjecture 16 of J. Arias de Reyna on the common denominators D_n of the Fabius function at dyadic rationals hold, and D_n is the least common denominator at level n. The Lean development builds on the public ProveIt Fabius library (MIT No Attribution), which supplies the definitions and the existence and uniqueness of the function. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $D_n$ be the denominator sequence associated with the rational values of the Fabius function, and define

$$
A_n=2^{-\binom{n}{2}}D_n.
$$

For $n\geq 1$, set $K_n=A_{2n-1}$; thus $K_1=A_1$, and for $n\geq 2$,

$$
K_n=2^{-\binom{2n-1}{2}}D_{2n-1}=2^{-\binom{2n-2}{2}}D_{2n-2}.
$$

Finally, define

$$
H_n=\frac{K_n}{2(2n-1)!}.
$$

**Conjectured arithmetic properties.** The following statements appear to be true: $A_{2n}=A_{2n+1}$ for $n\geq 1$; $2(2n-1)!$ divides $K_n$; and $H_n$ is an odd integer.

These claims describe a proposed parity and divisibility pattern for the normalized denominator sequence arising in the arithmetic of the Fabius function. The supplied text presents them as observations believed to hold, but gives no proof or resolution.

## Summary of the result

All three clauses of Conjecture 16 of Arias de Reyna on the common denominators of the values of the Fabius function at dyadic rationals hold: the stated coincidence of consecutive terms, the divisibility by 2(2n - 1)!, and the oddness and integrality of the normalized sequence H_n; moreover D_n is the least integer clearing all values of the function at the dyadic points of level n. Lean proves that a function satisfying the Fabius functional equation exists and is unique, derives its dyadic values from the moment recurrence, and proves the three clauses. The new mathematics is a triangular convolution with the Thue-Morse sequence, a propagation step through integer-valued polynomials, and a p-adic lemma on the first weighted minimum of a sequence of valuations.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
