# A nonvacuous reverse-mex counterexample

[MathDB 374728](https://mathdb.com/p/374728) proposes an equivalence between reverse mex and condition(a). For ordinary subtraction Nim S={3,6,10}, the actual Grundy sequence has prefix length12 and eventual period13. All source distance minima and condition(a) hold, with positive witness13 of distance4, but reverse mex fails at heap5.

The certificate verifies the exact all-heap mex recurrence, uniqueness, full source reduction, all13 residue distance minima, full prefix inclusion, and the universal condition. This is formal verification of Shivam Patel's already posted base counterexample. Its infinite scaling strengthening and other pass-game statements are not claimed. Pi GLM discovery work identified this existing source result for the campaign. No novelty or first-formalization claim is made.

The complete proof is in `main.tex` and `formal/ReverseMex.lean`. Run `python3 verify_outcome.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages` in a standalone package, or `python3 verify_outcome.py outcomes/reverse-mex` in the campaign. Lean4.34.1 and exact pinned dependencies are required. Source URLs, prior solution identifiers and content hashes accompany the package; full third-party snapshots remain in the separate local source audit.

Author Myeongjin Kang. AI-assisted. Original prose CC BY4.0; original code MIT. Existing mathematical counterexample credited to Shivam Patel.
