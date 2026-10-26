# Rust's known counterexample at index twenty

[MathDB 356369](https://mathdb.com/p/356369) records Rust's game-sequence conjecture, already disproved by Jeffrey Shallit in2022. This package verifies the same n=20 witness directly from the complete source greedy construction. It proves the infinite construction, exact history/selection/minimality and uniqueness bridges, the original seeds and positive-index histories, and the values30,56,86,84 giving170≠171.

The stronger published infinite-counterexample result is not claimed. No discovery or first-formalization claim is made. Pi's GLM discovery work identified this existing source result for the campaign. `main.tex` gives the complete proof and full finite witness table; `formal/Rust.lean` contains the entire kernel-checked certificate. Source URLs and exact content hashes accompany it; full third-party papers remain in the local source audit.

Run `python3 verify_outcome.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages` in a standalone package, or `python3 verify_outcome.py outcomes/rust` from the campaign. Lean4.34.1 and pinned dependencies are required. The verifier audits every local declaration and uses isolated source bytes; no native_decide or external computation oracle is used.

Author Myeongjin Kang. AI-assisted. Original prose CC BY4.0; original code MIT. Existing mathematical counterexample credited to Jeffrey Shallit.
