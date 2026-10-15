# Formal supporting lemmas

This is a separate, pinned Lean project for the 2026-10-14 frontier campaign.
It currently supports an **unaccepted candidate** and is not a formalization
of any complete research result.

## Reproduce

Install Lean through elan, then run from this directory:

```sh
lake update
lake build
lake env lean Audit.lean
```

`lean-toolchain` selects Lean 4.34.1. The dependency revision in
`lakefile.toml` fixes mathlib to
`d13f23b723b8a846827a245b89c10fc7d3f11612`; the checked-in manifest pins
its transitive dependencies. The update hook downloads precompiled mathlib
dependencies. The campaign's own proof terms are checked by Lean on build.

On the original research machine, Lean was already available at
`dlp-research/.tools/lean-4.34.1-linux/bin`; the parent used that binary
with this directory as the working directory. No files in that other
project were changed.

## Coverage

`FrontierSupport/LiftedEllipticity.lean` proves three statements over real
variables for the zero-jet quadratic form in I345 Section 7:

- an exact sum-of-squares decomposition;
- lower and upper quadratic bounds, uniformly over the stated parameters;
- the explicit uniform lower constant `b0^2/3`.

The real assumptions include `a^2+b^2=1`, `t^2<=1`, and `y>=0`.
The geometric interpretation sets `t=sqrt(e)` and `y` to a squared
perpendicular norm. The orthogonal coordinate split is explained in
`../p-gradient-parent/ellipticity.md`, but is **not** itself formalized.

The library contains no proof of weak/viscosity equivalence, compactness,
Savin's theorem, fitted-class Liouville rigidity, gradient extraction,
the complete p-uniform estimate, or novelty. No new research conclusion
is declared as an axiom. `Audit.lean` prints theorem dependencies so these
limits can be independently inspected.
