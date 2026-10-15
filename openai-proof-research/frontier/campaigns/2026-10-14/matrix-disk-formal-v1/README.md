# Finite real variance support for R024

Author: Myeongjin Kang, no affiliation. Original Lean/code: MIT (LICENSE).
Implementation: Pi/GLM-5.3-Flash; independent audit: parent Codex.

The byte-identical `FiniteVariance.lean` proves the finite real scalar
bistochastic triple-variance identity for any finite index type, its
per-column identity, and nonnegative deficit for nonnegative kernels.
The identity needs row/column normalization but no positivity. Empty
types are permitted. This is supporting algebra, not another frontier result.

**The full analytic theorem is not formalized.** In particular this file
does not formalize the Hilbert-valued integral/Fatou passage, exterior
conformal convergence, resolvent arguments, or geometric circle criterion.

Install the pinned Lean toolchain, then from this directory:

```sh
lake update
lake exe cache get
lake build
lake env lean Checks.lean
lake env lean ParentAudit.lean
```

The dependency revision is pinned in `lakefile.toml` and the transitive
lockfile. A clean machine needs network access and space for mathlib.
The cache command is optional for correctness, but avoids rebuilding
mathlib. The author-supplied `.olean` and local dependency cache are excluded.
The source compilation and the parent audit print axiom dependencies:
only `propext`, `Classical.choice`, `Quot.sound` for the three main theorems.

`Checks.lean` contains the implementing agent's extra examples, including
direct arithmetic; it is not an independent review. `ParentAudit.lean`
independently checks the exact generic statements and axiom lists.
The complete parent source review and fresh-compiler receipts are retained
in the sibling `matrix-disk-formal-review-r1` directory. The broader paper
and earlier review files remain frozen at their preparation-time status.
