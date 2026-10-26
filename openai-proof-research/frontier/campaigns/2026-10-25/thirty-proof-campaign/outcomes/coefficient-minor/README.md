# Three-matrix coefficient-minor stability

[MathDB 380287](https://mathdb.com/p/380287) is refuted by the explicit matrices in `main.tex`. The complete Lean proof includes every source hypothesis and the bridge to the actual source operator. `PROOF.md` explains coverage. This is formal verification of Shivam Patel's already posted counterexample, with no discovery or first-formalization claim.

Run `python3 verify_outcome.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages` in the standalone package. In the campaign run `python3 verify_outcome.py outcomes/coefficient-minor`. Lean 4.34.1 and the exact dependencies in pins.json are required. The isolated build prints every local declaration's type and transitive axioms.

`source.json` records primary-source and existing solution identifiers and retrieval hashes. Third-party full manuscripts and solution text are retained in the local source audit rather than redistributed. `main.tex` and the eventual paper PDF contain the full written proof. The independent review will be recorded before acceptance.

Author: Myeongjin Kang. AI-assisted. Original prose CC BY 4.0; original Lean code MIT. Existing mathematical counterexample credited to Shivam Patel.
