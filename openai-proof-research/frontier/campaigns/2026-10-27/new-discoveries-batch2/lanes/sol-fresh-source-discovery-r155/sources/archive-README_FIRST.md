# Read-once factorial-divisibility manuscript package - Version 2 source

This package is prepared as the source companion for Version 2 of
"The Read-Once Factorial-Divisibility Conjecture: Algebraic Proofs Through Six Inputs."
Version-specific Zenodo DOI: `10.5281/zenodo.21853500`.
It keeps the original Version 1 manuscript as the primary text, corrects and
clarifies several proof details, and adds the later four-input universal
constructions and a parity-pattern guide through six inputs.

## Scope retained from Version 1

- The main conjecture and the factorial-through-six theorem are unchanged.
- The abstract and future-work conclusion retain the Version 1 framing.
- The paper does not claim a general proof beyond six inputs.
- The added four-input guarantees are presented as additional constructions;
  no exact or optimal classification is claimed.
- The new four-input results are not propagated into a recomputed five- or
  six-input closure table.

## Added material

- Further universal four-input proofs for
  `17,19,21,22,23,25,26,27,28,30,32,33,35,40`.
- A parity-by-parity guide covering every odd/even pattern for `n=1,...,6` and
  pointing to the algebraic/congruence proof of the factorial target.
- Clear explanations that residual representative tables are finite signed
  residue-class classifications, not enumerations of integer inputs.
- `verify_residual_tables.py`, an optional standard-library-only consistency
  check for the residual lists used in the 17/19, 23, and 35 arguments.
- `VERSION_2_CHANGELOG.md`, a report of the substantive changes relative to
  the uploaded Version 1 source package.

## Compile

```bash
latexmk -xelatex -interaction=nonstopmode -halt-on-error manuscript.tex
```

## Optional residual-table check

```bash
python3 verify_residual_tables.py
```

The script is supplementary only; the manuscript's mathematical proofs are
self-contained.
