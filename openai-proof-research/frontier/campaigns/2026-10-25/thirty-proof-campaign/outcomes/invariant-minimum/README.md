# Minimum means and both invariance types

[MathDB 376980](https://mathdb.com/p/376980) records Horwitz's classification of pairs of means invariant in both types. The original PDF Conjecture29 (HTML26) adds no strictness to its continuous-mean definition. Binary and ternary minima satisfy full continuity, symmetry, internality and both identities, but admit no inverse quasi-arithmetic generator. The proof excludes every injective generator through an explicit inverse-formula bridge.

This is a counterexample to the literal formulation without strictness. The witness is not strict; no claim about a strengthened strict or analytic classification is made. No worldwide novelty or priority is claimed.

`main.tex` supplies the entire proof and scope discussion, `formal/InvariantMinimum.lean` the full certificate. Run `python3 verify_outcome.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages` in a standalone package, or `python3 verify_outcome.py outcomes/invariant-minimum` in the campaign. Lean4.34.1 and exact pinned dependencies are required. Provenance records original PDF/HTML label differences and hashes. Full third-party source snapshots are retained in the separate local audit rather than redistributed.

Author Myeongjin Kang. AI-assisted. Original prose CC BY4.0; original code MIT.
