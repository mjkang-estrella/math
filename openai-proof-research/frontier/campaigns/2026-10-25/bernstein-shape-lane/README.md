# Bernstein square-sum shape: MathDB 327180 (one outcome)

A complete Lean proof for every natural `n`, including `n = 0`, of convexity of the original Bernstein basis square-sum. The proof gives the stronger conclusion on all of `ℝ`. Symmetry, both half-line monotonicity statements, the global midpoint minimum, and its exact value are also kernel checked. Related MathDB 327181 and 327182 are corollaries in the same outcome.

- **Formal source:** `formal/BernsteinShape.lean`
- **Paper:** `paper/main.tex` and `paper/main.pdf`
- **Manifest:** `outcome.json`
- **Audit:** `build/audit.json`, `build/BernsteinShape.log`, `build/Checks.log`
- **Sources:** exact frozen MathDB JSON snapshots, full original and Nikolov PDFs, text extractions, and `sources/provenance.md`

## Exact bridge

`finite_average_identity` proves, without a representation hypothesis,

    phi n x = 1/(n+1) * sum_{j in ZMod(n+1)} ||x * stdAddChar j + (1-x)||^(2*n).

It is derived from `character_orthogonality`, `finite_parseval`, and `binomial_fourier`. Each summand is the power of the norm of a real affine map, hence convex. `bernstein_square_sum_convex` states the requested expanded binomial sum literally on `[0,1]`. `convexOn_univ` supplies global convexity.

The proposed positive central-binomial coefficient formula is independently derived for all `n` in the paper. It is not used by Lean. `check_identity.py` also checks its polynomial coefficients with exact integer arithmetic for `n = 0,...,32`; that finite regression is not the all-`n` proof.

## Reproduce verification

The toolchain and dependency revisions are pinned in `pins.json`. All package imports come from `../../2026-10-14/formal/.lake/packages`.

    python3 verify_without_git.py .

`verify_outcome.py` is a byte-identical copy of the campaign verifier. `verify_without_git.py` runs that verifier with only its dependency metadata queries replaced by read-only Dulwich calls (`optional_locks=False`). No Git executable is invoked. The pinned Dulwich wheel is under `tools/python`; it is used only for metadata inspection, never for the mathematical proof. The audit recompiles an isolated byte-identical module with warnings as errors and prints axioms for every declaration. No external theorem or unchecked representation enters the proof.

To rebuild the PDF from LaTeX using the local Tectonic binary:

    XDG_CACHE_HOME="$PWD/tools/cache" TMPDIR="$PWD/tools/tmp" tools/tectonic --keep-logs -o paper paper/main.tex

## Attribution and counting

This is a formalization of known mathematics, with no novelty or formalization-priority claim. Nikolov proved convexity in 2014. Gavrea and Ivan independently gave a Parseval-based proof in 2014. The original arXiv v1 already proves the midpoint minimum in Lemma 3.5, credited to Neuschel; the frozen 327182 source-status description is therefore inaccurate. See the precise source limitations and references in the provenance note and paper.

**Count one outcome, not three.** Independent parent review is pending. No sibling result, shared index, or repository commit is required for these artifacts.
