# MathDB 355956: The prime field is not a maximal clique in GP(5^8,3): a counterexample to Yip's maximal subfield clique conjecture

- Problem: https://mathdb.com/p/355956
- Source: Yip, J. Algebraic Combin. 56(2) (2022) 323-333, arXiv:2101.09652 Conjecture 1.4; Yip, Algebr. Comb. 6(4) (2023) 901-905, arXiv:2209.00864 Conjecture 1.1; MathDB 355956
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `MathDB355956.yip_conjecture_false : ¬ YipConjecture; MathDB355956.yip_conjecture_SG_false : ¬ YipConjectureSG`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `source-only-proof.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded primary-body, citing-work, web and registry comparison; not worldwide priority certification remaining_literature_limits: Yip PhD thesis unread; Three OpenAlex-listed citing works of the 2022 paper unread; MathDB/Palomar state inaccessible (403); Registry checks are path screens trust_limits: Prebuilt upstream Mathlib oleans trusted; no source-to-olean attestation; leanchecker shares the installation; Sampled private-RSS guard plus systemd MemoryMax; total VmRSS includes ~7 GB file-backed olean mappings not_claimed: Classification of failing (q,d); Exact clique number; Corrected sharp hypothesis; Worldwide priority; Publication or peer review
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: Yip's conjecture that the prime subfield is a maximal clique in the generalized Paley graph, in its unrestricted form. In every field with 5^8 elements, the prime subfield F_5 is a clique of GP(5^8,3) but not maximal: the element 2theta+4theta^2+theta^3, for theta a root of X^8+X^7+2X^6+2, extends it. The published theorem for q > (n-1)^2 is untouched. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

For q=5^8, d=3 (largest admissible r=1), in every field of order 5^8 the prime field F_5 is a clique of GP(5^8,3) but not maximal (x=2θ+4θ^2+θ^3, f(θ)=0, f=X^8+X^7+2X^6+2). Refutes the unrestricted conjecture; ALCO Theorem 1.2 (q>(n-1)^2) untouched.

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in source-only-proof.zip.
