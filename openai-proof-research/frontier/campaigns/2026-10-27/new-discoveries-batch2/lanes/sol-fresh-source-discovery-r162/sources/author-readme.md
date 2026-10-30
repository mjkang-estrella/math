# Degree–independent-domination bound for the saturation number

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21801900.svg)](https://doi.org/10.5281/zenodo.21801900)

This repository accompanies a short note by **Hassine Achour** proposing the following graph-theoretic conjecture:

> For every finite, simple, connected, nontrivial graph `G`,
> `s(G) <= ceil(Delta(G) i(G) / 2)`.

Here `s(G)` is the minimum cardinality of a maximal matching, `Delta(G)` is the maximum degree, and `i(G)` is the independent domination number.

## Status

Open conjecture. No proof or counterexample is claimed. The included computations are finite evidence only.

## Contents

- `paper.tex` and `paper.pdf`: short note.
- `code/check_delta_bound.py`: exact checker for a graph6 stream.
- `code/random_delta_bound.py`: reproducible random campaign.
- `code/txgraph/`: graph representation and exact invariant routines.
- `data/`: machine-readable campaign summaries.
- `tests/`: invariant and parser tests.

## Reproduce the checker

From the repository root:

```bash
PYTHONPATH=code python3 code/check_delta_bound.py < graphs.g6
```

Example exhaustive generation with nauty, one order at a time:

```bash
for n in $(seq 2 9); do nauty-geng -cq "$n"; done   | PYTHONPATH=code python3 code/check_delta_bound.py
```

The published summary reports 273,192 connected nonisomorphic graphs, zero violations, and 550 equality cases. Generation must be performed separately for each order; `geng 2:9` is not equivalent to this loop.

Run tests:

```bash
PYTHONPATH=code pytest -q
```

## Citation

See `CITATION.cff`. The archived preprint is available at [Zenodo, DOI 10.5281/zenodo.21801900](https://doi.org/10.5281/zenodo.21801900).

## License

Code is released under the MIT License. The note and documentation are released under CC BY 4.0.
