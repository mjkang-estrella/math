# MathDB 360458: The second q-analogue of Liu's Dwork congruence

- Problem: https://mathdb.com/p/360458
- Source: Victor J. W. Guo, “Dwork-type q-congruences through the q-Lucas theorem”, arXiv:2310.15207 (2023), Conjecture 6.2. https://arxiv.org/abs/2310.15207
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `Guo62.guo_conj_6_2`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Borderline significance: the reflection-at-roots toolkit is standard in this school and is shared with Liu and Tao (arXiv:2606.12037), which works at the level of values; the new content is the first-order shift-error cancellation for arbitrary m. The cross-model reviewer puts 0.55 on not routine and 0.60 on the verdict, at the floor root uses for counting. Prior-art clearance is bounded (access limits documented). No second cross-model lane read the finished Lean: root compared the final theorem and every definition with the endpoint the Claude Opus reviewer had written (identical), and the GPT-6.1 Sol final check verified nine exact cases modulo Φ_n^2 and their failure modulo Φ_n^3.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Guo's Conjecture 6.2 (arXiv:2310.15207), a q-analogue of Liu's Dwork-type supercongruence modulo Φ_n(q)^2 for every m >= 1 and n ≡ 1 (mod 4). The new step is a first-order cancellation of shift errors between complementary blocks at every primitive n-th root of unity. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $m$ and $n$ be positive integers with $n\equiv1\pmod 4$ and $n>1$, and let $(a;q)_k$ denote the $q$-shifted factorial. **The q-analogue conjecture.** $$\sum_{k=0}^{mn-1}\frac{(1+q^{4k+1})(q^2;q^4)_k^3}{(1+q)(q^4;q^4)_k^3}q^k\equiv \frac{[n]_{q^2}(q^3;q^4)_{(n-1)/2}}{(q^5;q^4)_{(n-1)/2}}q^{(1-n)/2}\sum_{k=0}^{m-1}\frac{(\frac12)_k^3}{k!^3}\pmod{\Phi_n(q)^2}.$$

## Summary of the result

The congruence holds for every m >= 1 and every n > 1 with n ≡ 1 (mod 4). Closest prior work: the block values in Guo's source, the base case from Guo and Zudilin (2020), and Guo's 2020 arbitrary-m result for n ≡ 3 (mod 4); the arbitrary-m statement modulo the square of the cyclotomic polynomial for n ≡ 1 (mod 4) was left open as Conjecture 6.2. The proof splits the left side into blocks of length n, shows that each block agrees with the right side's base value at every primitive n-th root of unity to first order (value and derivative), using a reciprocity under a shift of a parameter and a cancellation of the first-order shift errors between complementary blocks, and proves the base block by a terminating Dixon-type identity with an explicit WZ-style certificate. Lean works in the field of rational functions over Q with q the variable, states the congruence as coprimality of both denominators with Φ_n together with divisibility of the numerator of the difference by Φ_n^2, proves every denominator in the statement nonzero, and proves the base case rather than assuming it.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
