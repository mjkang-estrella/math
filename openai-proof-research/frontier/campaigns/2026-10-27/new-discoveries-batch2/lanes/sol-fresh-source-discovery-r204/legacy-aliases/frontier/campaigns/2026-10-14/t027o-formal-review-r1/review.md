# T027O scoped formal-support review, round 1

Verdict: **PASS_SCOPED_FORMAL_SUPPORT**

There are no required objections. Section 9 lists editorial items only.

This is an independent review of the scoped Lean package
`frontier/campaigns/2026-10-14/t027o-formal-v1/`. It audits only the new formal
claims and how they line up with the author's prose. It does not decide
whether T027O is correct as a whole, what it contributes, whether it is
accepted, or whether it counts toward the campaign total. The pinned upstream
theorems (revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`) are stipulated and
were not audited. Campaign counts played no part in this judgment.

## 1. Scope and outcome

The package claims exactly three things:

1. `T027O.triangle_coboundary`. This holds over any field and any index type,
   given a chosen reference index.
2. `T027O.principal_minor_rigidity`. Its hypotheses are: nonzero off-diagonal
   entries of `M`, zero diagonal of `E`, the explicit pair polynomials, the
   explicit six-term cycle polynomials, and unequal forward and reverse
   triangle products. It concludes `E i j = (h i - h j) * M i j`.
3. Rational 3x3 controls. One is a positive instance. The other is a proved
   counterexample, with no genericity, in which every stationarity identity
   holds but `E` is not a diagonal commutator.

Each claim is stated, compiled and documented accurately. The README and the
Lean header say that no determinant differentiation, genericity existence,
geometry, topology, arithmetic or orbit statement is formalized, and that is
correct. No `sorry`, `admit`, `unsafe`, `native_decide`, custom axiom or
notation override appears. Every declaration depends only on `propext`,
`Classical.choice` and `Quot.sound`.

This review also proves one link that the package explicitly leaves out, as an
independent check (`src/T027OReview.lean`, section 2). The package's pair and
cycle polynomials are exactly the first-order derivatives of the 2x2 and 3x3
principal minors of `M + tE`, once the lower-order stationarity identities
hold. So the hypotheses of `principal_minor_rigidity` are a faithful,
slightly weaker form of "every principal minor of size 1, 2 or 3 is
stationary". The package does not claim this link; the review supplies it as
evidence that the scoped lemma is meaningful.

## 2. Exact reads, all authenticated before use

| Object | SHA256 | Status |
|---|---|---|
| `t027o-formal-v1/manifest.json` (external anchor) | `b35948fddec735c7d9f0ed742d8158f4787f571cd69175a01f4db7ce2add46a4` | matches the caller's anchor; hashed before parsing |
| `t027o-formal-v1/T027O.lean` | `175680a36996718ad7fdf6aeb6fa5823c07d250e1b8bb43845a84c43e8a4e920` | matches the caller and the manifest |
| `t027o-formal-v1/Controls.lean` | `58b19c1037e343b0879f798daca4a6d4f62202f297456d27577e9d05f78adaf1` | matches the caller and the manifest |
| all 14 payload files and the `checks/` directory | see `results/input-authentication.json` | exact inventory matches the manifest (`verify.py`) |
| `fresh-arithmetic-discovery-r36/manifest.json` | `2127e23fd2698f75585c70ec4be93d599bb449c8d0f20a4bf6013a00cd7f0199` | matches the caller; pin `fd4aeeb2…` |
| `fresh-arithmetic-discovery-r36/candidate027o.md` | `e5812790dc336e2184ffbee58882fb154175554b9e23e0cacedeecac6bf48867` | matches the caller and the author manifest |
| `fresh-arithmetic-discovery-r36/scope027o.md` | `0f53abf319dfde7e8e1e88be77f98a5e0c423dcb0f9ffd99993088dc59b5cda2` | matches the caller and the author manifest |
| `fresh-arithmetic-discovery-r36/formal-interfaces.md` | `bf0174c7d0f1aff5b24a351a8f2376052de7b6eafb9e495d166f83c5d3441150` | matches the author manifest |

I read these in full before running anything: `AGENTS.md`, the campaign
acceptance rule (`frontier/NEW-TEN-2026-10-14.md`, line 15), the package README,
`T027O.lean`, `Controls.lean`, `checks/Checks.lean`, `rebuild.py`, `verify.py`,
`integrity_controls.py`, `lakefile.toml`, `lean-toolchain`,
`lake-manifest.json`, `checks/receipt.json` and `checks/types-axioms.log`. In
the author packet I read all of `scope027o.md` and `formal-interfaces.md`. In
`candidate027o.md` I read §4 (P1/P2, the principal-minor differential lemma and
its proof, lines 60–82) and the §6 applications that use it (lines 105–142,
specifically the steps at lines 121, 127 and 138). I did not read the rest of
the candidate as part of this review, and this review makes no judgment on it.

The frozen inputs were never modified. A full-tree SHA256 snapshot of
`t027o-formal-v1/` taken before all runs matches one taken after all runs (15
files). No `.olean`, `.lake` or `__pycache__` was created inside it. All Python
ran with `-B`.

## 3. Semantics, re-derived independently

### 3.1 `triangle_coboundary`

`∀ {K} [Field K] {ι} (o : ι) (x : ι → ι → K), (∀ i, x i i = 0) → (∀ i j, i ≠ j →
x i j + x j i = 0) → (∀ i j k, i ≠ j → j ≠ k → k ≠ i → x i j + x j k + x k i = 0) →
∃ h, ∀ i j, x i j = h i - h j`.

* **Witness:** `h i = x i o`, which matches the prose "h_i = x_i1". The
  conclusion is quantified over all `i j`, including `i = j`.
* **Cases, checked by hand:** `i = j` uses the diagonal hypothesis. `i = o`
  uses the pair `(o, j)`. `j = o` uses the diagonal at `o`. Otherwise use the
  triangle `(i, j, o)` together with the pair `(o, i)`.
* **No hidden assumptions:** no division and no characteristic assumption.
* **Degenerate cases:** the type `ι` must be nonempty (the reference index
  `o`), and the README discloses this as "chosen reference index". With one or
  two indices, the triangle hypothesis is vacuous and the result still holds.
  With empty `ι` the theorem does not apply, but its conclusion is trivially
  true there anyway.

### 3.2 `cycleDerivative` and `principal_minor_rigidity`

`cycleDerivative M E i j k` is the product-rule derivative of
`M_ij M_jk M_ki + M_ik M_kj M_ji`. I pinned this as an explicit six-term
expression (`pin_cycleDerivative`).

The theorem's hypotheses, in order, are:

* `hnz`: `M i j ≠ 0` for `i ≠ j`.
* `hdiag`: `E i i = 0`.
* `hpair`: `E_ij M_ji + M_ij E_ji = 0` for `i ≠ j`.
* `htri`: `cycleDerivative = 0` on ordered triples of distinct indices.
* `hgeneric`: `M_ij M_jk M_ki − M_ik M_kj M_ji ≠ 0` on ordered triples of
  distinct indices.

The conclusion is `∃ h, ∀ i j, E i j = (h i - h j) * M i j`.

* **Commutator form.** For a diagonal matrix `D = diag(h)`, the commutator
  `[D, M]` has entries `(h_i − h_j) M_ij`. So the entrywise conclusion is
  exactly the prose `E = [h0, M]`. `rigidity_from_minor_derivatives` restates
  it as a matrix identity over a `Fintype` index type.
* **Division.** The proof sets `x i j = E i j / M i j` off the diagonal, which
  is safe by `hnz`, and `x i i = 0`. It recovers `E = x * M` entrywise (by
  `hdiag` on the diagonal and `hnz` off it). It derives antisymmetry from
  `hpair` via `field_simp`.
* **Factorization.** After substituting, `cycleDerivative` factors as
  `(fwd − rev)(x_ij + x_jk + x_ki)`. I checked this by hand and in Lean. Then
  `hgeneric` and the fact that a field has no zero divisors give the triangle
  identity, and the coboundary theorem finishes the proof.
* **Characteristic.** No assumption on the characteristic is needed. Only
  division by the nonzero entries `M_ij` occurs. `positive_char5` gives a 4x4
  instance over `ZMod 5` with nonzero `E`.
* **Ordered triples.** Quantifying over ordered triples is equivalent to
  quantifying over unordered ones. `cycleDerivative_rotate` and
  `cycleDerivative_swap` show the cycle polynomial is invariant under all
  permutations. The `hgeneric` expression changes only by a sign under
  permutations, so it is equivalent to prose (4.1) "for every triple".
* **Hypothesis strength.** The prose assumes every principal minor is
  stationary. The Lean statement uses only sizes 1, 2 and 3, and the prose
  proof also uses only these sizes. So the Lean statement is at least as
  strong as the prose lemma, and its field is arbitrary rather than ℂ.

### 3.3 Mapping to the prose

| Prose (candidate §4, lines 74–80) | Lean |
|---|---|
| M has nonzero off-diagonal entries | `hnz` |
| (4.1) for every triple of distinct indices | `hgeneric` (ordered triples, which is equivalent) |
| 1x1 minors stationary give `E_ii = 0` | `hdiag`; my `minorDeriv_one` checks the bridge |
| 2x2 minors give `x_ij + x_ji = 0` | `hpair`; my `pair_iff_minor2` shows it is equivalent to the 2x2 derivative vanishing, given `hdiag` |
| 3x3 derivative: "diagonal and transposition terms vanish; what remains is (fwd−rev)(x_ij+x_jk+x_ki)" | `htri` uses only the remainder. My `minorDeriv_three` and `cycle_eq_minor3` formally prove that the diagonal and transposition terms vanish under `hdiag` and `hpair`, so `htri` is equivalent to the 3x3 derivative vanishing |
| `h_i = x_i1`, `h_1 = 0` | `triangle_coboundary` with `o` as the reference index |
| `E = [h0, M]`, h0 diagonal | entrywise conclusion; the matrix form is my `rigidity_from_minor_derivatives` |

The §6 applications (lines 127 and 138) instantiate the lemma with `M = NB` and
`M = BN`, where `B` is diagonal with nonzero entries. They then use
`[h0, NB] = [h0, N]B` and the fact that the triangle factors rescale by
`b_i b_j b_k`. These steps are elementary and correct, but they are **not**
formalized, and the package does not claim them. The steps behind the lemma's
hypotheses are also not formalized and not claimed: Vandermonde interpolation
(line 121), density of `C^l` in `T_C`, and the determinant derivative vanishing
by SL_r. The package's README matches `formal-interfaces.md` item 2 and
excludes items 1 and 3–7.

### 3.4 Assessment

The supporting lemma is meaningful. It is the exact algebraic core of the
candidate's principal-minor differential lemma, in a strictly stronger form
(any field, sizes 1–3 only). The hypotheses are jointly satisfiable with
nonzero `E`, and each hypothesis can be shown to be non-deletable (section 5).
The advertising is accurate, and the candidate itself does not claim
the lemma as new (line 82: Loewy and Mantelos are named as antecedents).

## 4. Trusted boundary

* **Compiler:** Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`,
  binary `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`,
  SHA256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
  The kernel and elaborator are trusted.
* **Library objects:** the shared, read-only cache at
  `frontier/campaigns/2026-10-14/formal/.lake/packages`. It has nine Git HEADs,
  all equal to the lockfile, with tracked files clean: mathlib
  `d13f23b723b8a846827a245b89c10fc7d3f11612`, plausible `118aa17e…`,
  LeanSearchClient `ddf04cf3…`, importGraph `e928b725…`, proofwidgets
  `106ff4fa…`, aesop `355695d5…`, Qq `6a489d9a…`, batteries `f2effa3d…`, Cli
  `e92c9f15…`. The `.olean` objects were **not** rebuilt from source and are
  trusted. Lean does not re-check imported declarations.
* **Mathlib imports:** the package imports only `Mathlib.Tactic`. The proofs
  use the tactics `linear_combination`, `field_simp`, `norm_num`, `fin_cases`,
  `simp` and `linarith`, plus core `decide`. Tactics produce kernel-checked
  terms, so they are not themselves trusted beyond producing those terms. The
  mathlib definitions the reviewer checks rely on are trusted: `Field`, `ZMod`,
  `Matrix.det_fin_one/two/three`, `Matrix.submatrix`, `Matrix.diagonal`,
  `Polynomial.derivative` and `Polynomial.eval`.
* **Axioms:** exactly `propext`, `Classical.choice` and `Quot.sound` for all 54
  checked declarations. That is 15 from the package and 39 from the reviewer.
  21 depend only on `propext` and `Quot.sound`.
* **Cache state:** I ran the author's rebuild with `GIT_OPTIONAL_LOCKS=0`.
  Before and after all runs, the `.git/index` mtimes and sizes of all nine
  cache packages were unchanged.

## 5. Commands and results

All writes went to the new scratch directory `/var/tmp/t027o-frev-r1-1792314513/`
and to this review directory, except the author's `integrity_controls.py`,
which writes only to its own `/var/tmp` temporary directory and removes it.

1. `sha256sum manifest.json T027O.lean Controls.lean` in the input gave the
   three caller hashes exactly.
2. `GIT_OPTIONAL_LOCKS=0 python3 -B rebuild.py --output /var/tmp/t027o-frev-r1-1792314513/author-rebuild`
   printed `PASS_SCOPED_SOURCE_BUILD_TYPES_AND_STANDARD_AXIOMS`, with 3 support
   and 12 control declarations, in about 8 seconds. The fresh `receipt.json`,
   `Checks.lean`, `support.log` (empty), `controls.log` (empty) and
   `types-axioms.log` are **byte-identical** to the recorded `checks/` files.
   The receipt SHA256 is `2f20d5ec…`; the types-axioms log SHA256 is
   `e5dae15b…`. The compiled objects lived only in the builder's temporary
   directory, which it deleted. Copies are in `results/author-rebuild/`.
3. `python3 -B verify.py --anchor b35948fd…` printed
   `PASS_IDENTITY_ONLY; no full theorem or independent formal-review verdict`.
   The same command with a 64-zero anchor gave `FAIL: external anchor mismatch`
   and exit code 1.
4. `python3 -B integrity_controls.py --anchor b35948fd…` (writes only to `/var/tmp`)
   accepted only the positive case. It rejected all 13 mutations: wrong-anchor,
   changed-source, missing-source, extra-file, extra-directory, root-link,
   ancestor-link, payload-link, payload-hardlink, fifo, manifest-hardlink,
   nested-manifest and self-reseal. No temporary directory was left behind.
   Output is in `results/author-integrity-controls.json`.
5. `python3 -B src/independent_build.py --output /var/tmp/…/final-build` is my
   own builder. It does not reuse `rebuild.py`; it re-authenticates the input
   anchor and the two source pins, and checks the compiler and the nine cache
   HEADs. It copies `T027O.lean` and `Controls.lean` byte-for-byte and adds
   `src/T027OReview.lean`. It scans comment-stripped sources for an extended
   forbidden list: `sorry`, `admit`, `unsafe`, `native_decide`,
   `implemented_by`, `extern`, `opaque`, `axiom`, `macro`, `elab`, `syntax`,
   notation keywords, `set_option`, `run_cmd`, `initialize`, `instance` and
   `local`. It allows only `def` and `theorem` declarations, tracking
   namespaces. It compiles in four steps (support, controls, review, and a
   `#check`/`#print axioms` file over all 54 declarations). The result was
   `PASS_INDEPENDENT_BUILD_TYPES_STANDARD_AXIOMS` with no warnings or errors.
   All objects were deleted after the run. The package portion of the
   types-axioms log is byte-identical to the recorded author log. A first
   scratch run, after iterating on my own file, gave an identical receipt.
   Results are in `results/independent-build/`.
6. `python3 -B src/input_controls.py` runs copied identity and Lean mutation
   controls on `/var/tmp` copies only (results in
   `results/input-controls.json`). The author's `verify.py`, run on mutated
   copies, rejects each mutation with the intended reason:
   * external-anchor mismatch: wrong anchor, edited manifest without
     resealing;
   * exact-inventory mismatch: a one-byte semantic edit of `hgeneric` from
     `≠ 0` to `= 0`, a changed control matrix, a deleted receipt, an extra
     check file, a README scope edit.

   Lean mutations of copies:
   * The unmodified baseline builds cleanly.
   * Deleting `hgeneric` gives an error.
   * Deleting `hpair` gives an error.
   * Flipping the sign of one cycle term makes `ring` fail.
   * Replacing the proof with `sorry` gives a "declaration uses `sorry`" warning,
     which is rejected.
   * Applying the theorem to the symmetric non-generic control leaves its
     genericity goal unsolved.

   The deletion cases fail mostly through name resolution. The mathematical
   necessity of each hypothesis is shown separately in Lean (below). The
   script asserts that the input tree's hashes are unchanged.

### Semantic controls, assessed

* **Nonvacuity.** `rigidity_positive_control` applies the theorem with every
  hypothesis discharged concretely. The control `genericE` is nonzero.
  Checking by hand, it equals `[diag(0,1,2), genericM]`, so the instance is
  consistent and nontrivial. `generic_witness` checks all six ordered triples.
* **Necessity of genericity.** In `symmetricM`, every off-diagonal entry is 1,
  so forward and reverse products agree on every triple. `cycleE` satisfies
  `hdiag`, `hpair` and the cycle identity on all triples, not only distinct
  ones. So all hypotheses except `hgeneric` hold.
  `not_diagonal_commutator` shows the conclusion fails: the triangle sum
  `x_01 + x_12 + x_20 = 3 ≠ 0` over ℚ. This is a real counterexample to
  deleting `hgeneric`, and it is also a counterexample to the prose lemma
  without (4.1). By my bridge theorems, every 1x1, 2x2 and 3x3 principal minor
  of `symmetricM + t·cycleE` is stationary.
* **My additions** (`src/T027OReview.lean`):
  * `degenerate_one` and `degenerate_two` show the theorem applies for one
    and two indices.
  * `positive_char5` gives a 4x4 instance over `ZMod 5` with nonzero `E`
    (`E5_ne_zero`), which exercises two reference-index triangles at once.
  * Each other hypothesis is non-deletable over ℚ, with every remaining
    hypothesis holding:
    * `drop_hdiag`: one index, `E = 1`;
    * `drop_hnz_others` and `drop_hnz_fails`: zero 2x2 `M`;
    * `drop_hpair_others` and `drop_hpair_fails`: 2x2 with `E = M`;
    * `drop_htri_others`, `drop_htri_violated` and `drop_htri_fails`: generic
      `M` with an antisymmetric cyclic `x`.
  * `author_control_char3` records that the author's genericity
    counterexample stops being one over `ZMod 3`, where `3 = 0`. That is
    consistent with the README, which states the control over ℚ.

Finite instances do not prove the general theorem. The general theorem rests
only on the kernel-checked proof of `principal_minor_rigidity`.

## 6. Reviewer Lean declarations (39, all standard axioms)

* **Statement pins:** `pin_triangle_coboundary`, `pin_cycleDerivative`,
  `pin_principal_minor_rigidity`.
* **Permutation invariance:** `cycleDerivative_rotate`, `cycleDerivative_swap`.
* **Derivative bridge:** `path`, `minorDeriv`, `minorDeriv_one`,
  `minorDeriv_two`, `minorDeriv_three`, `pair_iff_minor2`, `cycle_eq_minor3`,
  `rigidity_from_minor_derivatives`.
* **Degenerate and characteristic-5 cases:** `degenerate_one`,
  `degenerate_two`, `M5`, `h5`, `E5`, `E5_ne_zero`, `M5_nz`, `E5_diag`,
  `E5_pair`, `E5_cycle`, `M5_generic`, `positive_char5`.
* **Non-deletability:** `drop_hdiag`, `zM`, `zE`, `drop_hnz_others`,
  `drop_hnz_fails`, `pM`, `drop_hpair_others`, `drop_hpair_fails`, `tx`, `tE`,
  `drop_htri_others`, `drop_htri_violated`, `drop_htri_fails`.
* **Characteristic sensitivity:** `author_control_char3`.

`minorDeriv M E s` is the value at 0 of the formal derivative of
`det((M + X·E)[s, s])` in `K[X]`, so it is a genuine first-order
principal-minor variation.

## 7. Limitations

* This verdict covers only the three scoped package claims and how they align
  with candidate §4. It is not a verdict on T027O, its geometry, arithmetic or
  orbit density, or the §6 tangent certificate. It is also not a verdict on
  contribution, acceptance or count.
* Neither the package nor this review formalizes the reduction from
  characteristic coefficients to principal minors (Vandermonde, density of
  `C^l`), the existence of a generic `N` (P2), or the `NB`/`BN` rescaling. My
  bridge stops at derivatives of principal minors of a polynomial path.
* Mathlib and dependency objects were trusted, not rebuilt.
* The finite controls are illustrations. They are not evidence for the general
  theorem, which rests on the kernel-checked proof.

## 8. Required objections

None.

## 9. Editorial items (non-blocking)

1. README, "genericity assumption is mathematically necessary". More precisely,
   the hypothesis cannot be deleted: the control fails (4.1) at its only
   triple. It does not show that (4.1) is needed at every triple of a larger
   index set. The control is over ℚ; over a field of characteristic 3 the same
   `E` is a commutator.
2. README, "explicit pair … polynomials". The pair polynomial is minus the
   2x2 derivative only after `E_ii = 0`. The cycle polynomial is the 3x3
   derivative only after the diagonal and pair identities. Saying so would help
   readers; the bridge in this review confirms it.
3. `rebuild.py`:
   * It calls `git status` on the shared cache without `GIT_OPTIONAL_LOCKS=0`,
     so on a different machine it could refresh a cache index file. Setting
     that variable would make the cache strictly read-only.
   * The receipt fields `network_used` and `dependency_cache_modified` are
     constants, not measured values.
   * Its declaration regex recognizes only `def` and `theorem`, and its
     `axiom` scan only matches at the start of a line. This is adequate for the
     present sources and is backed by `#print axioms`, but it is brittle.
4. `integrity_controls.py` checks only the exit code, not the rejection reason.
   `results/input-controls.json` records the reasons.

## 10. Review packet identity

The exact inventory is sealed in `review-manifest.json`, whose SHA256 is the
external anchor reported to the caller and is not recorded inside this
directory. Run `python3 -B verify.py --anchor <ANCHOR>` to check it (read-only,
identity only). `python3 -B review_controls.py --anchor <ANCHOR>` runs copied
mutation controls on `/var/tmp` copies of this directory. Its results are
reported to the caller after sealing and are not part of the sealed inventory.
