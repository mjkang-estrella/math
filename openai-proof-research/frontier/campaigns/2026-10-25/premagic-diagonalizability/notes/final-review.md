# Final independent review

**Verdict: PASS.** No substantive correctness, conjecture-match, definition,
formal-coverage, or attribution findings. No critical, high, medium, or low
severity defects were identified in the reviewed snapshot.

Review date: 2026-10-25 (America/Los_Angeles). This is an independent AI review,
not external human peer review. Read and followed the project `AGENTS.md`.
Reviewed `paper/main.tex`, all of `formal/Premagic.lean`, `Checks.lean`,
`rebuild.py`, pins, source records and retained source text, existing mathematical,
source and formal audits, `COVERAGE.md`, `PROVENANCE.md`, and the diagnostic code.
Only this review file was written. The parent retains responsibility for final
rebuilds, PDF/release inspection, and archive integrity.

## Exact target and definitions

The retained MathDB record identifies problem 336488 and its assertion that
premagic matrices are diagonalizable and have a full-rank eigenvector system.
The retained arXiv v2 and journal texts agree: Definition 4.3 equates corresponding
row and column sums, and Conjecture 7.2 asserts diagonalizability. I also checked
the live [arXiv v2 text](https://arxiv.org/html/1706.08856v2), Definitions 4.3–4.5
and Conjecture 7.2. No symmetry, invertibility, zero-diagonal, or stochasticity
hypothesis is imposed by that conjecture. The live MathDB API was inaccessible
through the web tool; the retained API record was read and its recorded hash
verified. No fresh claim about current database status is needed for this review.

Lean's `Premagic` is exactly the corresponding-sum equality, without requiring
a common sum across different indices. `Diagonalizable` quantifies over mutually
inverse square matrices and an actual diagonal matrix. This is ordinary
similarity, not orthogonal diagonalization or a surrogate kernel condition.
`diagonalizable_iff_similarity` and `diagonalizable_iff_inv` explicitly connect
the definition to the usual invertible-similarity formula. Non-diagonalizability
also refutes the full-rank eigenvector clause: a basis of eigenvectors would
supply precisely such a similarity. No definition has been weakened.

## Mathematical verification

- **Main matrix:** All nine entries of `M` are positive integers and every row
  and column sums to 9. With the paper's vectors `u=(1,-1,0)` and `v=(1,1,-2)`,
  `Mu=0` and `Mv=6u≠0`. For a diagonal matrix over a field,
  `d_i²x_i=0` implies `d_ix_i=0`; similarity transports this implication.
  Therefore the chain proves non-diagonalizability over **both R and C**.
  Lean uses the equally valid smaller chain
  `(1,0,-1) -> (3,-3,0) -> 0`.
- **Shifted family:** The displayed basis `P=(1,u,v)` has determinant 6, and
  `A_t P=P [[t+9,0,0],[0,t,6],[0,0,t]]`. Thus the characteristic polynomial
  is `(X-(t+9))(X-t)^2` and the determinant is `(t+9)t²`.
  For every real `t≥0`, the entries are positive and all sums are `t+9`;
  for `t>0`, invertibility follows. Subtracting `tI` from any hypothetical
  diagonalization reduces to the main obstruction, including over C.
- **Stochastic family:** Division by `t+9>0` gives positive entries and unit
  row and column sums. A nonzero scalar multiple is diagonalizable exactly
  when the original is, over either field. The stated characteristic polynomial
  follows by scaling. At `t=1`, the repeated eigenvalue is `1/10`, its eigenspace
  is one-dimensional, and the dominant eigenvalue 1 is simple. There is no
  conflict with the claimed dominant-eigenvalue behavior.
- **General dimension:** Zero-padding `u,v` preserves their zero sums,
  `v^Tu=0`, and `v^Tv=6`. In `3J_n+uv^T`, the rank-one perturbation has entries
  at least -2, so entries are at least 1; row/column sums are `3n`.
  The same nontrivial chain works for every `n≥3`. This proves the written
  extension, rather than merely extrapolating finite numerical examples.
- **Minimality:** For real order-two matrices, the premagic equations force
  equal off-diagonal entries, hence real symmetry and diagonalizability.
  Order one is immediate. The paper correctly limits this minimality claim
  to real matrices. Indeed, the complex symmetric premagic matrix
  `[[i,1],[1,-i]]` is nonzero with square zero, confirming why that caveat matters.

## Actual formal coverage and build evidence

The main C non-diagonalizability theorem is fully formal:
`not_diagonalizable` applies to every characteristic-zero field, and
`main_counterexample` explicitly includes `¬ Diagonalizable (M C)` alongside
the real positivity, premagic and non-diagonalizability assertions.
Scalar-shift non-diagonalizability is likewise formal over all such fields.

**The formal `B_t` is R-only.** Its positivity, doubly stochastic property,
premagic property and non-diagonalizability are proved over R. Its C
non-diagonalizability is supplied by the paper's valid scaling argument, not by
a separately stated Lean theorem. The paper and `COVERAGE.md` state this boundary
accurately. Characteristic polynomials, determinants, the displayed Jordan
basis, eigenspace dimensions, real minimality and arbitrary-dimension extension
are written mathematics rather than separately certified Lean statements.
Their use does not overstate the formal result.

Independently reconciled all 37 declarations (8 definitions, 29 theorems)
against both `#check` and `#print axioms` directives and the compiler transcript.
All reported axioms lie in `{propext, Classical.choice, Quot.sound}`. No `sorry`,
`admit`, `native_decide`, or custom axiom occurs. The kernel-square proof derives
the needed implication from the similarity witnesses; it does not assume it.

Reviewed `rebuild.py`'s version/dependency pin gates, manifest agreement,
tracked-source checks, complete declaration auditing, warning-as-error builds,
fresh module outputs and axiom allowlist. The successful audit's five source
hashes match the current files. I did not rerun the compiler or modify its
outputs while the parent was rebuilding. As the existing formal audit states,
precompiled dependency libraries remain a trust boundary; source pin checks
are not a fresh rebuild of those libraries.

Independently reran the read-only exact-rational diagnostic: PASS for the main
chain, sums, ranks, characteristic polynomial, four shifted stochastic cases,
the Jordan basis, and 30 higher-dimensional shifted cases. These computations
support, and do not replace, the universal arguments. All six retained source
manifest entries match their byte counts and SHA-256 hashes.

## Attribution and novelty

The paper identifies the original definition/conjecture, arXiv version/date,
published version, and MathDB selection record. Source statements establish
the target and terminology; no disputed upstream theorem is a proof premise.
The bounded prior-art search and unread subscription-only 2026 chapter are
disclosed in existing notes/provenance. The package makes no worldwide-priority
or external-peer-review claim and distinguishes the explicit checked disproof
from a new general spectral technique. No source/novelty correction is required.

## Reviewed snapshot (SHA-256)

| File | Hash |
| --- | --- |
| `paper/main.tex` | `752f87b7e1d0d5a6738e766590a6ac39311b78fc618ce597a701d0804f815fdc` |
| `formal/Premagic.lean` | `eb49447c957f122baf2221ed9939ff9dc2a755651ca6729da59865cda4c46f1c` |
| `formal/Checks.lean` | `257e37adbd9817bc9a8b655ca1899567c523ba492d2ff0c9c36e0477577dc1f3` |
| `formal/rebuild.py` | `f53c13387625d39141c8425bf069d6b2ed3d91518c5790478838d0185e8c6c36` |
| `COVERAGE.md` | `626a73c510446c1540fe145ce1a4917312fad8df47fc0564b355ca7cf9089a6f` |
