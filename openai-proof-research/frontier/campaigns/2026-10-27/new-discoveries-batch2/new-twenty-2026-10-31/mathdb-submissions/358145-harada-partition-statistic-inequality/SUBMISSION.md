# MathDB 358145: Harada partition-statistic inequality

- Problem: https://mathdb.com/p/358145
- Source: S; u; g; i; m; o; t; o; 2; 3; 0; 4; .; 1; 0; 7; 0; 8; v; 3;  ; E; q; 3; .; 2; /; C; o; n; j; 5; .; 2;  ; a; n; d;  ; o; w; n; e; d;  ; j; o; u; r; n; a; l;  ; D; O; I; 1; 0; .; 2; 2; 1; 0; 8; /; i; j; g; t; .; 2; 0; 2; 4; .; 1; 4; 0; 8; 8; 8; .; 1; 8; 9; 6
- Outcome: **PROVED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Harada.target_proved : Harada.Target`, `Harada.integerTarget_proved : Harada.IntegerTarget`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `PAPER-v1.md`, `EXACT-LEAN-APPENDIX-v1.md`
- Lean source: `mathdb-358145-proof-packet.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Positive bounded primary-method comparison and substantive target-specific mechanism; not newness inferred from formalization, open label, absent hits or worldwide-absence claim. remaining_literature_limits: Separate Abe/Hida-Sugimoto journal versions not authenticated; inspected deposited primary versions compared.; Registry coverage is complete current preprint metadata and documented catalogue result statements, not every manuscript proof.; Retrieved normalized target snapshot, not live canonical-page status. not_claimed: Worldwide priority guarantee; Historically spotless process; Publication or upload; New proof truth of imported pinned upstream theorems
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: the Harada partition-statistic inequality. For every n >= 7, the quantity binom(n,2) times the partition number p(n), minus the sum of the statistic Psi over all partitions of n, is positive, where Psi uses the number of positive parts, the weighted length, and products of consecutive hook lengths as in Harada's fishhook theory; no finite-group integrality theorem is claimed. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

For every integer n>=7, D(n)=binom(n,2)*p(n)-sum_{lambda partitions n}Psi(lambda)>0, where p counts all ordinary partitions, L is positive row count, T=sum_i(i-1)lambda_i, h_j=column length and Psi=binom(L,2)+T+sum_{j>=1}h_j*h_{j+1}, with zero column tails. No full finite-group integrality theorem is credited.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER-v1.md. The complete Lean source is in mathdb-358145-proof-packet.zip.
