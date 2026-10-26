# Formal implementation and independent audit

Date: 2026-10-25. Scope: this `formal/` directory only. No paper, index,
upstream source, dependency cache, commit, or publication was modified. The
requested ultrafast service tier was confirmed in the inherited runtime options.

## Result

`Premagic.lean` compiles with Lean 4.34.1 and mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`. `Checks.lean` prints the types and
transitive kernel axiom dependencies of all **37 local declarations: 8 definitions
and 29 theorems**. Every reported axiom belongs to:

- `propext`
- `Classical.choice`
- `Quot.sound`

There are no `sorry`, `admit`, `native_decide`, or user axiom declarations in the
Lean sources. The compiler runs with `-DwarningAsError=true`; final builds have no
warnings. `build/Checks.log` is the full type/axiom transcript;
`build/audit.json` records the toolchain, dependency revisions, source SHA-256
hashes, declaration count, allowlist result, and exact `LEAN_PATH`.

## Definition audit

`Premagic A` means coordinatewise equality of the row-sum and column-sum
vectors: for every index `i`, `∑ j, A i j = ∑ j, A j i`. This does not require
all row sums to be the same. The witness actually satisfies the stronger
condition that all row and column sums equal 9.

`Diagonalizable A` explicitly quantifies over square matrices `P`, `Q` and a
diagonal vector `d`, with `P Q = I`, `Q P = I`, and `A = P diag(d) Q`.
This is standard diagonalizability over the named coefficient field, not
orthogonal/unitary diagonalization and not a condition only at eigenvalue zero.
Two formal equivalence theorems now make the interpretation explicit:

- `diagonalizable_iff_similarity`: equivalence to the two inverse identities
  together with `Q A P = diag(d)`.
- `diagonalizable_iff_inv`: equivalence to `∃ P d, IsUnit P ∧
  P⁻¹ A P = diag(d)`, using mathlib's matrix inverse and `IsUnit`.

The second theorem proves the quantified `Q` equals `P⁻¹`. Conversely, mathlib's
inverse identities follow from the explicit `IsUnit P`. Thus there is no reliance
on the totalized inverse of a singular matrix. The standard elementary
interpretation is that the columns of `P` are a basis and `A P = P diag(d)` makes
them eigenvectors. No separate bridge to a library eigenspace-spanning predicate
is claimed or needed; the conventional invertible-similarity definition itself
is formally equivalent.

`DoublyStochastic A` explicitly includes entrywise nonnegativity and unit row and
column sums. `B_t_positive` proves strictly positive entries, stronger than the
nonnegativity clause. All statements concern square `Fin 3` matrices unless the
theorem type explicitly generalizes the finite index type.

## Independent kernel-square audit

For any field and any finite square matrix index type, `square_kernel` proves
that diagonalizability implies `A(Ax)=0 → Ax=0`. If `A=P D Q` and `QP=I`,
applying `Q` twice reduces the premise to `D²(Qx)=0`. In coordinate `i` this is
`d_i (d_i (Qx)_i)=0`; the field's zero-product property implies
`d_i (Qx)_i=0`. Multiplication by `P` gives `Ax=0`. Injectivity of multiplication
by `P` follows directly from `QP=I`. In particular:

- no spectral theorem, root existence, algebraic closure, or Jordan normal form
  is assumed;
- characteristic zero is not needed for the kernel-square lemma;
- the lemma is an implication, not a proposed characterization of all
  diagonalizable matrices;
- it is a vector statement precisely sufficient for the explicit chain below.

For

```text
M = [4 4 1; 2 2 5; 3 3 3],
u = (1,0,-1),  v = (3,-3,0),
```

the exact products are `Mu=v` and `Mv=0`. `v ≠ 0` follows from its first
coordinate `3 ≠ 0` in every characteristic-zero field. Hence `M²u=0` while
`Mu≠0`, contradicting the kernel-square conclusion. The Lean proof uses these
explicit products, with exact arithmetic and no floating-point computation.
`CharZero` is a sufficient hypothesis; the file does not claim it is necessary
or classify positive-characteristic cases.

## Exact formal coverage

| Declarations | Formally checked content |
| --- | --- |
| `chain_image`, `kernel_image` | The two exact matrix-vector identities, over every field. |
| `square_kernel` | Kernel-square implication over every field and finite square index type. |
| `not_diagonalizable` | `M K` is not diagonalizable for every field `K` with `CharZero K`. |
| `row_sum`, `column_sum`, `premagic` | All row/column sums of `M K` are 9, hence premagic. |
| `positive` | All nine entries of `M ℝ` are strictly positive. |
| `main_counterexample` | Positivity and premagic over ℝ, and failure of diagonalization over both ℝ and ℂ. |
| `diagonalizable_iff_similarity`, `diagonalizable_iff_inv` | The conventional similarity definitions above are equivalent. |
| `diagonalizable_sub_scalar`, `diagonalizable_smul` | Subtracting any scalar identity and multiplying by any scalar preserve diagonalizability. |
| `A_t_not_diagonalizable` | For every characteristic-zero field `K` and every `t : K`, `A_t K t = M K + t I` is not diagonalizable. |
| `A_t_row_sum`, `A_t_column_sum`, `A_t_premagic` | Both sets of sums are `9+t`, for arbitrary `t` over every field. |
| `A_t_positive` | `A_t ℝ t` has strictly positive entries whenever `0 ≤ t`. |
| `B_t_positive`, `B_t_row_sum`, `B_t_column_sum` | For real `t ≥ 0`, `B_t t = (9+t)⁻¹ A_t ℝ t` is strictly positive with all sums 1. |
| `B_t_doubly_stochastic`, `B_t_premagic`, `B_t_not_diagonalizable` | The same normalized family is doubly stochastic, premagic, and not diagonalizable over ℝ. |
| `exists_premagic_not_diagonalizable`, `not_all_premagic_diagonalizable` | Explicit existential and universal-negation statements in dimension 3 over every characteristic-zero field. |
| `exists_positive_premagic_not_diagonalizable`, `not_all_positive_premagic_diagonalizable` | The positive real dimension-3 versions, with the positivity hypotheses inside the quantified propositions. |
| `exists_positive_doubly_stochastic_not_diagonalizable` | An explicit existential positive doubly stochastic real counterexample, using `B_t 0`. |

The shift proof subtracts `t I` from a hypothetical diagonalization of `A_t`,
obtaining one of `M`. The normalized proof multiplies a hypothetical
diagonalization by `9+t`, obtaining one of `A_t`. For `t≥0`, `9+t>0`, so the
normalizing factor exists, is positive, and cancels exactly. All hypotheses and
quantifiers are visible in `Checks.lean`'s output.

## Reproduction

From any working directory, run (substitute local paths as needed):

```sh
python3 /path/to/formal/rebuild.py \
  --lean-bin /path/to/lean-4.34.1-linux/bin/lean \
  --mathlib-packages /path/to/.lake/packages
```

Equivalent environment configuration is:

```sh
LEAN_BIN=/path/to/lean-4.34.1-linux/bin/lean \
MATHLIB_PACKAGES=/path/to/.lake/packages \
python3 /path/to/formal/rebuild.py
```

The defaults locate this workspace's supplied Lean and the 2026-10-14 campaign's
package directory. The script uses only the Python standard library, `git`, and
the chosen `lean` executable; it does not invoke Lake or install anything.
`pins.json` records Lean, mathlib, and all eight manifest dependency revisions.
Before compilation the script verifies the Lean version, local `lean-toolchain`,
every dependency Git HEAD, tracked-source cleanliness, and manifest agreement.
It rejects incomplete/duplicate checks, forbidden proof tokens, missing axiom
reports, and axioms outside the allowlist.

All generated files go in `formal/build/`. The script removes its own previously
generated module outputs, recompiles `Premagic.lean`, then compiles `Checks.lean`
against that fresh result. The source directory itself is excluded from
`LEAN_PATH`, so the preexisting adjacent `Premagic.olean` cannot satisfy the
import. `LEAN_PATH` includes the new build directory followed by
`<package>/.lake/build/lib/lean` for mathlib and **every** manifest dependency.
The supplied `Cli` checkout has no such cache directory; its path is still
included, and these imports do not require a Cli module. No dependency cache is
created or changed. A failed invocation removes the prior `audit.json` success
record, so stale success cannot masquerade as the latest result.

Validated invocation modes:

1. Default paths: successful compilation and axiom audit.
2. Both explicit path options: successful compilation and axiom audit.
3. Both environment variables, launched from `formal/build/`: successful
   compilation and axiom audit.
4. An incompatible executable (`/usr/bin/true`): rejected at the version gate.
5. A package directory without the required checkouts: rejected before compilation.

The last successful run is recorded in `build/rebuild.log`, the explicit-options
run in `build/explicit-options.log`, and negative inputs in
`build/negative-checks.log`.

## Boundaries and residual issues

No gap was found in the original kernel-square argument or the main
counterexample. The local proof does not assume the MathDB336488 claim: it
provides a counterexample to the universal premagic-diagonalizability statement.
Identification and quotation of the external MathDB source, the paper narrative,
and novelty assessment remain the parent's responsibility. No upstream theorem
is imported as a custom axiom.

The formal file does not claim a characteristic-polynomial calculation, minimal
polynomial, Jordan normal form, exact eigenspace dimensions, sharp parameter
ranges for positivity, or a positive-characteristic classification. Positivity
of `M` and the normalized family is formalized over ℝ; `M`'s complex
nondiagonalizability is separately formalized. Nondiagonalizability of the real
normalized family after changing scalars to ℂ is not a separately stated theorem.

Rebuilding uses the supplied precompiled dependency libraries. Git pin and
cleanliness checks certify their source checkouts, and Lean validates compatible
imports; this script does not independently rebuild or cryptographically prove
the provenance of those cached libraries. This is the explicit dependency trust
boundary required by the instruction not to alter caches.
