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

`FrontierSupport/VectorEllipticity.lean` adds seven theorems in an arbitrary
real inner product space. They establish the Gram nonnegativity bound,
exact square decompositions, and both bounds for the actual vector form

    Q(a,h,b,e,s) = ‖h‖² + (1+e)s² - (⟪a,h⟫ + b√e s)².

The final `physical_uniform_bounds` theorem assumes `‖a‖²+b²=1`,
`0<=e<=1`, and `b0²<=b²`. It proves

    (b0²/3)(‖h‖²+s²) <= Q <= 2(‖h‖²+s²).

This includes the square-root substitution and needs no coordinate split.
It is the dimension-independent zero-jet form used in the manuscript.
The scalar module remains available, with assumptions `a²+b²=1`,
`t²<=1`, and `y>=0`. There are ten supporting lemmas in total; these are
not ten research results and do not add an accepted campaign result.

The library contains no proof of weak/viscosity equivalence, compactness,
Savin's theorem, fitted-class Liouville rigidity, gradient extraction,
the complete p-uniform estimate, or novelty. No new research conclusion
is declared as an axiom. `Audit.lean` prints theorem dependencies so these
limits can be independently inspected.
