# Lane summary: pi-connection-dirac-formal

**Status: COMPLETE (sub-lane scope).** `formal/DiracPositive.lean` compiles cleanly
(0 errors, 0 warnings) against the pinned toolchain and the parent lane's frozen
modules. All new declarations depend only on the standard Lean axioms
(`propext`, `Classical.choice`, `Quot.sound`) — verified via `#print axioms`.
No `sorry`/`admit`/`axiom`/`unsafe`/`native_decide`.

## Deliverable 1 — positive-Dirac-eigenvector normalization (generic)

For any real matrix `C : Matrix V F ℝ`, `D = fromBlocks 0 C Cᵀ 0` on
`EuclideanSpace ℝ (V ⊕ F)`, and any orthonormal family `w : ι → ...` of
D-eigenvectors with eigenvalues `μ i > 0`:

- `diracPos_inner_half` : `⟪a i, a j⟫ = ⟪b i, b j⟫` (adjointness of the two block
  equations; holds for `μ i + μ j > 0`, i.e. for any pair of positive eigenvalues,
  repeated eigenvalues included — no rank/nullity argument).
- `diracPos_orthonormal` : `u i = √2 • (vertex component of w i)` is an
  `Orthonormal ℝ` family in `EuclideanSpace ℝ V`.
- `diracPos_eigenvector` : `u i` is a `C * Cᵀ`-eigenvector with eigenvalue `μ i ^ 2`.

## Deliverable 2 — Dirac spectral upper bounds (graph specialization, C = signedIncidence E)

Namespace `ConnectionGraph`, file `formal/DiracPositive.lean` (imports
`GraphMatrices`, `Variational` — byte-identical copies of the parent's frozen
modules live in this formal dir so the `.olean`s resolve via cwd).

- `dirac_spectral_top_sum_le_sqrt (E) (hk : k ≤ Fintype.card V) :
     spectralTopSum (diracMatrix E) k ≤ √(2 * k * sortedTopSum (degree E) k)`.
  Note: needs **no** `ValidEdges E` hypothesis. Route: the positive selected
  eigenvalues `μ i` give an ON family `u i` (Deliverable 1) with
  `∑ μ i² ≤ 2 · sortedTopSum (degree E) r`, `r = #Sp ≤ k` (monotonicity in `k`
  of `sortedTopSum` for nonnegative arrays, proved here as
  `sortedTopSum_mono_of_nonneg`), then Cauchy–Schwarz
  (`sq_sum_le_card_mul_sq_sum` / `sum_le_sqrt_card_mul_sq_sum`) plus
  `Real.le_sqrt`. Dropping nonpositive eigenvalues can only increase the
  top-k sum (`sum_le_sum_pos_part`).
- `dirac_spectral_top_sum_le_global (E) (hE : ValidEdges E) (hk : k ≤ v + m) :
     spectralTopSum (diracMatrix E) k ≤ E.card + Fintype.card V / 2`.
  Route: `2μ ≤ μ² + 1` termwise; `∑ μ² ≤ 2m` from the Bessel bound
  `diracPos_ON_energy_le` (∑ over ON family of `⟨u, Cᵀe⟩² ≤ ‖Cᵀe‖² = 2`,
  per edge; needs `ValidEdges E` for the column-norm lemma
  `signedIncidence_column_sq`); `r ≤ v` from orthonormality
  (`Orthonormal.linearIndependent` + `LinearIndependent.fintype_card_le_finrank`
  with `finrank_euclideanSpace`).

## Reusable lemmas for the parent lane

- `sortedTopSum_mono_of_nonneg (f) (hf : ∀ i, 0 ≤ f i) (hrk : r ≤ k) :
     sortedTopSum f r ≤ sortedTopSum f k` — generic, `[Fintype α] [DecidableEq α]`.
  If the parent wants it, it can be copied under its own name (it is *not* in
  parent's TopSums/Variational).
- `sq_sum_le_card_mul_sq_sum`, `sum_le_sqrt_card_mul_sq_sum` — Cauchy–Schwarz
  helpers over finite types.
- `diracPos_ON_energy_le` — ON family energy bound `⟪u, L u⟫ ≤ 2#E` (Bessel).
- `signedIncidence_column_sq` — column of the signed incidence matrix has
  squared norm 2 (requires `ValidEdges E`).
- `sum_le_sum_pos_part` — dropping nonpositive entries from a Finset sum.

## Build instructions

```
cd .../lanes/pi-connection-dirac-formal/formal
python3 ../../parent-means/formal/run_lean.py DiracPositive.lean   # compile check
# .olean (already present): LEAN_PATH=$PWD:<packages> lean -o DiracPositive.olean DiracPositive.lean
```
Log: `../logs/final_compile.log` (empty = clean run). Verification of axioms and
signatures: rerun with `#print axioms` / `#check` (see summary above for outputs).

## Honest caveats / gaps

- These are *supporting* bounds for the parent's endpoint
  `S_k(L) − S_k(D) ≥ √2 − 1`; **the parent theorem is not proved here and no
  credit is claimed**. The comparison step (L vs D, all k, K₅ counterexample
  exclusion) remains the parent lane's task.
- `dirac_spectral_top_sum_le_sqrt` is stated for `k ≤ v` only (the global
  `k ≤ v+m` case is covered by the cruder `m + v/2` bound). A sharper
  `k ≤ v+m` sqrt bound would need an argument for `k > v` (edge-side
  eigenvectors), not attempted here.
- The `.olean` was produced by this lane; if the parent integrates, it should
  recompile from source in its own checkout (parent frozen at e6bde404e1
  owns its build graph).
- Implementation author is not the final reviewer of these bytes.
