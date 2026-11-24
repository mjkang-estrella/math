# MathDB 361410: Parity congruence conjecture for finite Mordell--Tornheim sums

- Problem: https://mathdb.com/p/361410
- Source: Crystal Wang and Jianqiang Zhao, “Mordell–Tornheim Zeta Values, Their Alternating Version, and Their Finite Analogs”, arXiv:2401.03380 (2024). https://arxiv.org/abs/2401.03380
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `FiniteMT.wang_zhao_conjecture_3_4`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Bounded literature search. The citing-paper check was completed in part by root and a second cross-model lane after the GPT-6.1 Sol final check had left eligibility in doubt: of the seven papers citing McCoy et al., the one that could overlap, Wang and Ma, arXiv:2511.23308 (2025), was read in full and treats only depth 3 with exponents (1, 1, 1), a case the source itself attributes to earlier work; Shen 2024 (doi 10.1155/2024/8445635) could be read only in abstract (triple reciprocal sums modulo p^2, r = 1). The list of papers citing the source itself could not be fetched (rate limits). Cross-model confidence: correct 0.85 (every step checked by hand, 660 brute-force cases), not routine 0.65, not public 0.95 for the papers read. The printed example for p = 13 is proved modulo 13^5; its sharpness modulo 13^6 is computed, not formalized. No second cross-model lane read the finished Lean: the statement file is byte-identical to the one that reviewer confirmed as literal.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. All five congruences of Conjecture 3.4 of Wang and Zhao (arXiv:2401.03380) for the finite Mordell-Tornheim-type sums Z_{p^r}^{d}(s) modulo powers of p hold, for general exponent vectors s, every r >= 1 and the stated depths. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $r\in\N$, let $p$ be a prime, and let $\bfs\in\N^d$ satisfy $p>|\bfs|+1$, where $|\bfs|$ is the weight and $Z_{p^r}(\bfs)$ is the corresponding finite Mordell--Tornheim sum. **Finite Mordell--Tornheim congruence conjecture.** The following congruences should hold:

1. If $d=4$ and $|\bfs|$ is odd, then

$$
Z_{p^r}(\bfs)\equiv p^{2r-2}Z_p(\bfs)\pmod{p^{2r-1}}.
$$

2. If $d=4$ and $|\bfs|$ is even, then

$$
Z_{p^r}(\bfs)\equiv p^{r-1}Z_p(\bfs)\pmod{p^r}.
$$

3. If $d=5$ and $|\bfs|$ is even, then

$$
Z_{p^r}(\bfs)\equiv p^{2r-2}Z_p(\bfs)\pmod{p^{2r-1}}.
$$

In general, if $r\geq2$ and $d+|\bfs|$ is odd, then

$$
Z_{p^r}(\bfs)\equiv0\pmod{p^{2r-2}};
$$

if $r\geq2$ and $d+|\bfs|$ is even, then

$$
Z_{p^r}(\bfs)\equiv0\pmod{p^{r-1}}.
$$

The conjecture extends parity-dependent congruences for finite Mordell--Tornheim sums beyond the cases proved earlier in the paper. It is supported by extensive numerical evidence, while the stated general assertions remain open.

## Summary of the result

All five assertions of Conjecture 3.4 of Wang and Zhao hold: for a prime p exceeding the weight plus one, every r >= 1 and every exponent vector s of positive integers, the finite sums Z_{p^r}^{d}(s) over compositions of p^r into d positive parts prime to p satisfy the stated divisibility by powers of p, the scaling laws in depths 4 and 5 relating level p^{r+1} to level p^r, and the general recurrence in r. Earlier work (Chen and Zhao; McCoy, Thielen, Wang and Zhao) treated only exponents all equal to 1, where just the last assertion applies; the source proved depth 3 by Bernoulli-number computations. The proof lifts the sum from level p^r to p^{r+1} keeping double precision (modulus p^{2r+1}), shows that the second moments of the carries vanish modulo p, and projects onto one reflection parity to gain a further factor of p. Lean states the sums and the five congruences literally in the integers modulo prime powers.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
