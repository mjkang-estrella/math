# Ordinary versus symplectic quadratic differences

[MathDB 358595](https://mathdb.com/p/358595). The quadratic-difference equivalence fails on the real symplectic plane for p=q=X²+1 and the zero endomorphism.

Formal verification of the dimension-two specialization of the counterexample already given by Clément de Seguins Pazzis in the primary source, and identified in his MathDB reply; no discovery/priority claim.

The full proof is in `main.tex` and `formal/QuadraticDifference.lean`; `PROOF.md` maps source hypotheses and conclusions to the certificate. Source corrections and prior-art credit are retained in the paper and provenance. Full third-party snapshots remain in the local source audit; their URLs and content hashes accompany this package.

Run `python3 verify_outcome.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages` in the standalone package, or `python3 verify_outcome.py outcomes/quadratic-difference` in the campaign. Lean 4.34.1 and the dependencies pinned in pins.json are required. The isolated verifier audits every local declaration's type and transitive axioms.

Author Myeongjin Kang. AI-assisted. Original prose CC BY 4.0; original code MIT. No discovery or first-formalization claim.
