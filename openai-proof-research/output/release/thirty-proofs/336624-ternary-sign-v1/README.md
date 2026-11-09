# A printed alternating-sign correction

[MathDB336624](https://mathdb.com/p/336624) and the actual cited source, Kiss–Somlai Conjecture5.3, equation24, print coefficients(-1)^i starting at1. The real ternary heap x-y+z is associative, idempotent, strictly coordinate-monotone and nonreducible by any associative binary operation, yet no bijection represents it with the printed signs. The complete proof of every hypothesis, arbitrary binary-reduction obstruction, and exact finite-sum bridge is in Lean.

This is a literal sign correction. The heap itself appears in the cited source's Example4.10. With signs(-1)^(i+1), the identity bijection represents it, so the intended corrected classification is not refuted. No substantive classification solution or worldwide novelty is claimed. Both original PDF v3 and HTML v1/v3 were checked; the stronger v3 strictness assumption is met.

Run `python3 verify_outcome.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages` in the standalone package, or `python3 verify_outcome.py outcomes/ternary-sign` in the campaign. Lean4.34.1 and pinned dependencies are required. `main.tex` supplies the complete written proof; `primary-reference.json` records exact source versions and hashes. Full third-party papers remain in the local audit rather than redistributed.

Author Myeongjin Kang. AI-assisted. Original prose CC BY4.0; original code MIT; known heap example credited to Kiss–Somlai.
