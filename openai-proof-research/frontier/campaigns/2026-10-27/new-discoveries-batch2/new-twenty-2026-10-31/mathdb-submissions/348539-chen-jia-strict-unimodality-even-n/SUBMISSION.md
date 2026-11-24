# MathDB 348539: Strict unimodality conjecture for Reiner–Stanton polynomials

- Problem: https://mathdb.com/p/348539
- Source: William Y. C. Chen and Ivy D. D. Jia, “Semi-invariants of Binary Forms Pertaining to a Unimodality Theorem of Reiner and Stanton”, arXiv:2011.01467 (2021). https://arxiv.org/abs/2011.01467
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `ChenJia.chen_jia_conj_3_3`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Do not say 'resolves Conjecture 3.3' without 'for even n'. The source's definition (3.4) and the MathDB record restrict n to even, and the theorem proves that statement in full; but the conjecture's sentence does not repeat the restriction, the paper's example F_{5,9} has odd n, and the threshold k >= 15 is explained only by odd n, so the authors very probably meant both parities (the cross-model reviewer puts 0.25 on even-only being intended). For odd n with odd k the strict single-peak property fails by symmetry (for example F_{9,15}); with a central tie allowed the odd case holds numerically for n up to 41 and is open; nothing here applies to it. Computer-assisted: 364 of the 605 Lean modules are generated certificate data. The journal text of section 3 was not available. Cross-model confidence: mathematics 0.9, novelty 0.8, Lean statement equals the record 0.97.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved for even n. For every even n >= 8 and k >= 15, F_{n,k}(q) = [n+k, k]_q - q^n [n+k-2, k-2]_q is symmetric with f_0 = f_1 and strictly increasing from f_1 to the centre. This is Chen and Jia's Conjecture 3.3 (arXiv:2011.01467) in the setting of their definition (3.4), n even, as the MathDB record states it. The case of odd n is not covered. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let

$$
F_{n,k}(q)={n+k\brack k}-q^{n}{n+k-2\brack k-2},
$$

where $k\geq 2$ and $n$ is even. A polynomial is **strictly unimodal, except for the two terms at both ends** when its coefficients strictly increase to the middle, apart from the two end terms. **Strict unimodality conjecture.** For $n\geq 8$ and $k\geq 15$, $F_{n,k}(q)$ is strictly unimodal, except for the two terms at both ends. The conjecture is supported by numerical evidence, while the text does not report a proof or disproof.

## Summary of the result

For every even n >= 8 and every k >= 15, the polynomial F_{n,k}(q) = [n+k, k]_q - q^n [n+k-2, k-2]_q is symmetric of degree nk, has f_0 = f_1, and its coefficients increase strictly from f_1 up to the centre nk/2. This is Conjecture 3.3 of Chen and Jia in the setting of their definition (3.4), where n is even, which is also how the MathDB record states it. The proof works in the ring of semi-invariants of binary forms modulo the unique invariant Q of degree 2: that quotient is a domain, so the set of degrees in which a coefficient difference is positive is closed under addition; Sylvester's theorem identifies the differences with dimensions; uniform seeds in a few small degrees come from a quasipolynomial certificate for restricted partitions (3,632 residue cases, each a polynomial identity plus a sign check, with the coverage of all cases proved in Lean); a covering argument and a separate induction for n = 10 and 14 finish. Lean defines the Gaussian binomial as a sum over partitions in a box and proves the statement literally.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
