# Schur stability: MathDB 370245

Complete rational counterexample, proof, and single-module Lean certificate for both assertions of Banerjee–Chaudhury Conjecture 1.1. This is the s=1 specialization of Shivam Patel's posted family, supplied by the parent; no novelty or priority claim.

- [Full proof and coverage](PROOF.md)
- [Lean module](formal/SchurStability.lean)
- [Paper source](paper/main.tex) and [rendered paper](paper/main.pdf)
- [Campaign manifest](outcome.json)
- [Source provenance and hashes](metadata.json)
- [Kernel audit receipt](build/audit.json)
- [Self-review](self-review.md)

The certificate proves every source hypothesis, actual inversion, complete complex spectra, exact mathlib spectral radii, nonzero eigenvectors, and separate refutations of the two universal dimension-two claims. No mathematical or formal gap remains for this specialization. Independent parent review is pending.

## Verify

From this directory:

```bash
python3 verify_without_git.py .
```

The default compiler is `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`, version 4.34.1. The default package path is `../../2026-10-14/formal/.lake/packages`. To relocate:

```bash
python3 verify_without_git.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages
```

The campaign verifier is copied byte-for-byte into `verify_outcome.py`. `verify_without_git.py` delegates to it, replacing only the two read-only Git metadata queries with Dulwich; optional index refresh is disabled. The helper Python packages under `tools/python` were copied from the already installed campaign tooling. No git executable is invoked.

A direct compile is also available through `./check.sh -DwarningAsError=true formal/SchurStability.lean` from this directory (or provide an absolute Lean file path). The audited route is preferred because it builds an isolated copy and inventories every declaration.

## Render the paper

```bash
./build_paper.sh
```

Requires Tectonic and Poppler. Set `TECTONIC=/path/to/tectonic` if necessary. On this host the script falls back to the existing Tectonic 0.15.0 binary in the neighboring Bernstein lane. Its cache is local to this lane. The paper builds entirely from cached TeX resources with no TeX warnings; all four rendered pages were inspected. Rendered pages are retained under `paper/rendered`.

All changes and generated files are confined to this lane. No shared indexes, commits, additional agents, or external postings were created.
