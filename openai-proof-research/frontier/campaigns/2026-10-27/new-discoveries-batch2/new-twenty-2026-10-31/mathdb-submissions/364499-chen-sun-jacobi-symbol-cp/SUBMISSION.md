# MathDB 364499: The Jacobi-symbol conjecture for the integers $c_p$

- Problem: https://mathdb.com/p/364499
- Source: Deyi Chen and Zhi-Wei Sun, “On determinants involving (j^2-k^2p) and (jkp)”, arXiv:2408.14401 (2024). (https://arxiv.org/abs/2408.14401), Conjecture 1.1
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `ChenSun.chen_sun_conjecture`, `ChenSun.jacobi_cp_eq_one`, `ChenSun.chen_sun_conjecture_with_root`, `ChenSun.even_root_exists`, `ChenSun.odd_signed_root`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Low to modest significance (user may overrule). No citing papers were found; arXiv keyword search and Google Scholar could not be used, and some 2026 journal papers were read only through reference lists. Related work by Ren and Luo (arXiv:2407.04556) uses similar methods on other matrices.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. For every odd prime p, let c_p be the positive odd integer defined by the determinant identities of Chen and Sun (their Theorem 1.1). Then the Jacobi symbol (p / c_p) equals 1, which is their Conjecture 1.1. The proof combines a Vandermonde factorization modulo p with an integer skew-block identity when p is 1 modulo 4 and a signed Pfaffian evaluation when p is 3 modulo 4; existence and uniqueness of c_p are proved along the way. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $p$ be an odd prime. For $\delta\in\{0,1\}$, define

$$
D_p^{(\delta)}(w)=\left|\left(\frac{j^2-k^2}{p}\right)+\left(\frac{jk}{p}\right)w\right|_{\delta\leqslant j,k\leqslant(p-1)/2}-\left|\left(\frac{j^2-k^2}{p}\right)\right|_{\delta\leqslant j,k\leqslant(p-1)/2}.
$$

For $p\equiv1\pmod4$, let $c_p$ be the positive odd integer whose existence is asserted by the preceding theorem through $D_p^{(0)}(w)=-w((p-1)c_p/2)^2$; for $p\equiv3\pmod4$, let $c_p$ be the positive odd integer whose existence is asserted through $D_p^{(1)}(w)=w(c_p\sum_{k=1}^{(p-1)/2}(\frac{k}{p}))^2$.

**Jacobi-symbol conjecture for $c_p$.** For any odd prime $p$,

$$
\left(\frac{p}{c_p}\right)=1,
$$

where $(\frac{p}{c_p})$ is the Jacobi symbol.

The conjecture is based on numerical values of $c_p$ listed in the source. The supplied text gives no resolution or proof, so its status remains open.

## Summary of the result

For every odd prime p, the Jacobi symbol (p / c_p) equals 1, where c_p is the positive odd integer defined by the determinant identities of Chen and Sun (Theorem 1.1 of the source); existence and uniqueness of c_p are proved as part of the statement. This is Conjecture 1.1 of the source. Orientation matters: with c_p on top the symbol is -1 for 16 of the 80 odd primes up to 419. The proof uses a Vandermonde factorization, an integer skew-block identity for p = 1 mod 4, and a signed Pfaffian with its square identity and a character evaluation for p = 3 mod 4. Significance is low to modest (review 0.3).

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
