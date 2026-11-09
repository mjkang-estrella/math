import SourceOrdered

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace PeakonCoefficients

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem trace_submatrix_permutation (M : Matrix n n ℂ) (e : Equiv.Perm n) :
    Matrix.trace (M.submatrix e e) = Matrix.trace M := by
  exact Equiv.sum_comp e (fun i => M i i)

theorem pow_submatrix_permutation (M : Matrix n n ℂ) (e : Equiv.Perm n) (m : ℕ) :
    (M.submatrix e e) ^ m = (M ^ m).submatrix e e := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, pow_succ, ih, Matrix.submatrix_mul_equiv]

omit [Fintype n] [DecidableEq n] in
theorem sourceLax_permutation (r : n → ℂ) (q : n → ℝ) (nu lam xi : ℂ) (e : Equiv.Perm n) :
    sourceLax (r ∘ e) (q ∘ e) nu lam xi = (sourceLax r q nu lam xi).submatrix e e := rfl

theorem sourceHamiltonian_permutation (r : n → ℂ) (q : n → ℝ) (nu gamma : ℂ)
    (e : Equiv.Perm n) (k : ℕ) :
    sourceHamiltonian (r ∘ e) (q ∘ e) nu gamma k = sourceHamiltonian r q nu gamma k := by
  unfold sourceHamiltonian
  change (k : ℂ) * Matrix.trace (
    (sourceT r q nu + (gamma / 2) • sourceA r q nu).submatrix e e *
      (sourceS r q nu + sourceA r q nu).submatrix e e ^ (k - 1)) = _
  rw [pow_submatrix_permutation, Matrix.submatrix_mul_equiv, trace_submatrix_permutation]

theorem sourceTrace_permutation (r : n → ℂ) (q : n → ℝ) (nu lam xi : ℂ)
    (e : Equiv.Perm n) (m : ℕ) :
    Matrix.trace (sourceLax (r ∘ e) (q ∘ e) nu lam xi ^ m) =
      Matrix.trace (sourceLax r q nu lam xi ^ m) := by
  rw [sourceLax_permutation, pow_submatrix_permutation, trace_submatrix_permutation]

variable {N : ℕ}

def descendingPositionPermutation (q : Fin N → ℝ) : Equiv.Perm (Fin N) :=
  Tuple.sort (fun i => -q i)

theorem positions_sorted (q : Fin N → ℝ) : Antitone (q ∘ descendingPositionPermutation q) := by
  have hm := Tuple.monotone_sort (fun i => -q i)
  intro i j hij
  have h := hm hij
  exact neg_le_neg_iff.mp h

theorem source_trace_partition (r : Fin N → ℂ) (q : Fin N → ℝ) (nu lam xi gamma : ℂ)
    (hcurve : xi ^ 2 = lam ^ 2 + gamma * lam + 1) (m : ℕ) (hm : 0 < m) :
    Matrix.trace (sourceLax r q nu lam xi ^ m) =
      ∑ j ∈ Finset.range m, ∑ p ∈ (Finset.Icc 1 N).sym (j + 1),
        if p.val.sum = m then coefficientWeight (K := ℂ) m p.val * lam ^ (j + 1) *
          (p.val.map (sourceHamiltonian r q nu gamma)).prod else 0 := by
  have h := source_trace_partition_ordered (r ∘ descendingPositionPermutation q)
    (q ∘ descendingPositionPermutation q) nu lam xi gamma (positions_sorted q) hcurve m hm
  rw [sourceTrace_permutation] at h
  simpa only [Fintype.card_fin, sourceHamiltonian_permutation] using h

end PeakonCoefficients
