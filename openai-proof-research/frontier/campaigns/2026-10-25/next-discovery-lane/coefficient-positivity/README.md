# MathDB 372794: ready for parent review

**Full outcome:** For every natural r and every pair of natural exponents i,j, the coefficient of t^i a^j in the exact Fill--Janson polynomial h(t,a;r) is nonnegative.

**Status:** the complete Lean module passes the pinned verifier. Independent parent review is pending, so this lane has not counted or released it as accepted.

## Source

Fill and Janson, arXiv:2601.19323v1, Appendix E, Lemma E.8(a), (E.16), Conjecture E.9 (PDF printed page 38).

The exact fetched post, including all posted solutions, is in `source.json`; raw response and original papers are archived in `../sources/`. `primary-reference.json` records hashes and the credited reply.

## Proof

Write x=1+at and A=(x+3t)(x+2t), B=(x+t)(x+4t), C=(x+t)(x+2t), D=x(x+3t), K=8t^4(x+2t). The homogeneous expression H_n=(x+2t)A^n-(x+4t)B^n+(x+2t)C^n-xD^n has auxiliary sequences U_n=H_(n+1)-DH_n and V_n=U_(n+1)-CU_n. Initial values H_0=U_0=0,V_0=K and recurrence V_(n+1)=BV_n+KA^(n+1), together with H_(n+1)=DH_n+U_n and U_(n+1)=CU_n+V_n, prove simultaneous coefficientwise positivity by induction. The source substitution is proved algebraically in Lean.

## Deliverables

- `main.tex`: detailed manuscript; `build/main.pdf`: built paper.
- `formal/CoefficientPositivity.lean`: complete single-module proof.
- `formal/Checks.lean`: declaration and axiom checks, copied from the pinned verifier.
- `build/audit.json`: compiler receipt; `build/Checks.log`: full declaration/axiom output.
- `coverage.json`, `NOVELTY.md`, `self-review.md`: scope and review notes.

Run from the campaign directory:

```sh
python ../twenty-proof-campaign/verify_outcome.py coefficient-positivity
```

The verifier uses Lean 4.34.1 and the already installed package revisions in `pins.json`. The canonical main theorem is `CoefficientPositivity.all_coefficients_nonnegative`. Its module has 24 audited declarations. No omitted proof placeholders or non-kernel computation are present.

## Limits

This resolves the integer-exponent coefficient question in full. It does not formalize the separate real-exponent probability or root conjectures in the source paper.

The MathDB record contains an earlier proof by Shivam Patel (2026-08-20, solution UUID 46acd5c9-9ae6-4584-a626-588caaf59c7b). It uses a positive rational generating function. A live search also found Machina Mathematica / Korea Superintelligence Labs, “Swap differences of powers”, https://ideosphere.ai/papers/fill-janson-coeff, with a 2026-09-07 snapshot and an already reported Lean proof of this exact conjecture. No mathematical novelty, first-proof, or first-formalization claim is made. This packet is a fresh local implementation of a known result, through a triangular recurrence. The external dossier was used for novelty assessment and is not imported into the Lean proof.
