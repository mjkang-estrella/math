# MathDB 366674: A q-analogue of the Van Hamme–Sun supercongruence equivalence

- Problem: https://mathdb.com/p/366674
- Source: Victor J. W. Guo and Chen Wang, “Refinements of Van Hamme's (E.2) and (F.2) supercongruences and two supercongruences by Swisher”, arXiv:2501.09626 (2025), Conjecture 4.1. https://arxiv.org/abs/2501.09626
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `GuoWang.guo_wang_conj_4_1`, `ReviewEndpoint.guo_wang_conj_4_1`, `GuoWang.reviewed_source_form`, `GuoWang.poch_den_ne_zero`, `GuoWang.Clear.diff_five_num_ne_zero`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Borderline significance: the techniques are the standard toolkit of this school, and the earlier results give lower powers of Φ_n (Guo and Zudilin the square; Wang, Tian and Huang the cube for one side); the cross-model reviewer puts 0.55 on not routine and 0.50 on the verdict, at root's counting floor. The congruence of rational functions is read through the numerator of the reduced difference, which is the only meaningful reading for composite n (individual terms carry Φ_d for d | n in their denominators). The journal body was not read; prior-art residual risk about 5 percent after the final check identified the fourth citing work as unrelated. The Lean was written by GPT-6.1 Sol lanes and packaged by a Claude Opus 5.5 lane; the final check was by a separate Opus lane (same model family as the packager) because GPT-6.1 Sol hit its usage limit; a Sol re-check after 2026-11-26 is advisable.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Guo and Wang's Conjecture 4.1 (arXiv:2501.09626): for every positive n ≡ 1 (mod 4) the two q-series sums (q-analogues of Van Hamme's (E.2) and (F.2)) agree modulo [n]Φ_n(q)³, by a common q-WZ recurrence with matching first-order boundary terms at the roots of unity. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $n\equiv 1\pmod{4}$ be a positive integer. Define the $q$-integer $[m]=(1-q^m)/(1-q)$, the $q$-shifted factorial $(x;q)_k=(1-x)(1-xq)\cdots(1-xq^{k-1})$, and let $\Phi_n(q)$ denote the $n$-th cyclotomic polynomial. **q-analogue conjecture.** $$\sum_{k=0}^{n-1}(-1)^k[6k+1]\frac{(q;q^2)_k^3}{(q^4;q^4)_k^3}q^{3k^2} \equiv \sum_{k=0}^{n-1}(-1)^k[8k+1]\frac{(q;q^4)_k^3}{(q^4;q^4)_k^3}q^{2k^2+k} \pmod{[n]\Phi_n(q)^3}.$$

## Summary of the result

The congruence holds modulo [n]Φ_n(q)³ for every positive n ≡ 1 (mod 4). The proof finds a common finite q-WZ recurrence for the two sides under the parameter shift a → aq⁴, with matching boundary terms, which gives divisibility of the difference by Φ_n(q)⁴ at every primitive n-th root of unity, and treats the proper divisors d of n (whose Φ_d divide [n]) by a separate cancellation. Lean states the congruence as divisibility of the numerator of the reduced difference by [n]Φ_n(q)³ in ℚ[q], proves the only denominator in the statement nonzero, includes the review's required statement verbatim, and proves that the difference is not zero at n = 5.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
