# Insufficiency of Pfaffian invariants for symplectic congruence

[MathDB 381863](https://mathdb.com/p/381863). Two real nonsingular skew-symmetric 6-by-6 forms, neither scalar J, have all three source Pfaffian invariants equal but belong to different symplectic congruence orbits.

Formal verification of Shivam Patel’s posted 6-by-6 counterexample; no discovery or first-formalization claim.

The full proof is in `main.tex` and `formal/SymplecticOrbits.lean`; `PROOF.md` maps source hypotheses and conclusions to the certificate. Source corrections and prior-art credit are retained in the paper and provenance. Full third-party snapshots remain in the local source audit; their URLs and content hashes accompany this package.

Run `python3 verify_outcome.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages` in the standalone package, or `python3 verify_outcome.py outcomes/symplectic-orbits` in the campaign. Lean 4.34.1 and the dependencies pinned in pins.json are required. The isolated verifier audits every local declaration's type and transitive axioms.

Author Myeongjin Kang. AI-assisted. Original prose CC BY 4.0; original code MIT. No discovery or first-formalization claim.
