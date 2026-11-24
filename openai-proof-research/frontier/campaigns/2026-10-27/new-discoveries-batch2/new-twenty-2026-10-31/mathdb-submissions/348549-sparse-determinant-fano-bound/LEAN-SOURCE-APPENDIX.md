# Lean source appendix — MathDB 348549 (COMPLETE)

All modules, including both unconditional endpoints, are printed byte-for-byte in import order.

### `SparseStatement.lean`

```lean
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open scoped BigOperators
open Matrix Finset

namespace SparseDet

/-- Literal source alphabet: integer entries equal to zero or one. -/
def ZeroOne {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∀ i j, A i j = 0 ∨ A i j = 1

/-- Nonzero entries, exactly as counted in the printed conjecture. -/
def edges {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Finset (Fin n × Fin n) :=
  univ.filter (fun p => A p.1 p.2 ≠ 0)

def edgeCount {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : ℕ := (edges A).card

def rowDegree {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : ℕ :=
  ∑ j, if A i j ≠ 0 then 1 else 0

def colDegree {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) : ℕ :=
  ∑ i, if A i j ≠ 0 then 1 else 0

def PrintedConjecture : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ),
    (∀ i j, A i j = 0 ∨ A i j = 1) →
    (univ.filter (fun p : Fin n × Fin n => A p.1 p.2 ≠ 0)).card ≤ 3 * n →
    ((A.det : ℤ) : ℝ) ≤ (24 : ℝ) ^ ((n : ℝ) / 7)

def IntegerConjecture : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ),
    (∀ i j, A i j = 0 ∨ A i j = 1) →
    (univ.filter (fun p : Fin n × Fin n => A p.1 p.2 ≠ 0)).card ≤ 3 * n →
    |A.det| ^ 7 ≤ (24 : ℤ) ^ n

lemma edgeCount_eq_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    edgeCount A = ∑ i, ∑ j, if A i j ≠ 0 then 1 else 0 := by
  classical
  simp only [edgeCount, edges, card_filter]
  rw [Fintype.sum_prod_type]

lemma edgeCount_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    edgeCount A.transpose = edgeCount A := by
  simp only [edgeCount_eq_sum, Matrix.transpose_apply]
  exact Finset.sum_comm

lemma rowDegree_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    rowDegree A.transpose i = colDegree A i := rfl

lemma colDegree_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    colDegree A.transpose i = rowDegree A i := rfl

lemma identity_zeroOne (n : ℕ) : ZeroOne (1 : Matrix (Fin n) (Fin n) ℤ) := by
  intro i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

lemma identity_edgeCount (n : ℕ) : edgeCount (1 : Matrix (Fin n) (Fin n) ℤ) = n := by
  classical
  rw [edgeCount_eq_sum]
  simp [Matrix.one_apply]

lemma identity_satisfies (n : ℕ) :
    (∀ i j, (1 : Matrix (Fin n) (Fin n) ℤ) i j = 0 ∨
      (1 : Matrix (Fin n) (Fin n) ℤ) i j = 1) ∧
    (univ.filter (fun p : Fin n × Fin n =>
      (1 : Matrix (Fin n) (Fin n) ℤ) p.1 p.2 ≠ 0)).card ≤ 3 * n := by
  refine ⟨identity_zeroOne n, ?_⟩
  change edgeCount _ ≤ _
  rw [identity_edgeCount]
  omega

lemma order_zero (A : Matrix (Fin 0) (Fin 0) ℤ) :
    A.det = 1 ∧ ((A.det : ℤ) : ℝ) ≤ (24 : ℝ) ^ ((0 : ℝ) / 7) := by
  simp

/-- The real-power bridge has no matrix-side assumptions. -/
lemma real_bound_of_integer_bound (n : ℕ) (z : ℤ)
    (hz : |z| ^ 7 ≤ (24 : ℤ) ^ n) :
    (z : ℝ) ≤ (24 : ℝ) ^ ((n : ℝ) / 7) := by
  have hcast : |(z : ℝ)| ^ 7 ≤ (24 : ℝ) ^ n := by exact_mod_cast hz
  have hp : 0 ≤ (24 : ℝ) ^ ((n : ℝ) / 7) := Real.rpow_nonneg (by norm_num) _
  have hid : ((24 : ℝ) ^ ((n : ℝ) / 7)) ^ (7 : ℕ) = (24 : ℝ) ^ n := by
    calc
      _ = (24 : ℝ) ^ (((n : ℝ) / 7) * 7) := by
        simpa only [Nat.cast_ofNat] using
          (Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 24) ((n : ℝ) / 7) 7).symm
      _ = (24 : ℝ) ^ (n : ℝ) := by congr 1; ring
      _ = (24 : ℝ) ^ n := Real.rpow_natCast _ _
  have habs : |(z : ℝ)| ≤ (24 : ℝ) ^ ((n : ℝ) / 7) := by
    exact le_of_pow_le_pow_left₀ (by decide : (7 : ℕ) ≠ 0) hp (hid.symm ▸ hcast)
  exact (le_abs_self _).trans habs

#print axioms identity_satisfies
#print axioms order_zero
#print axioms real_bound_of_integer_bound
end SparseDet
```

### `SparseSanity.lean`

```lean
import SparseStatement
import Mathlib.Tactic.NormDet
import Mathlib.Tactic.FinCases

open Matrix Finset
namespace SparseDet

def fano : Matrix (Fin 7) (Fin 7) ℤ :=
  !![1,1,0,1,0,0,0;
     0,1,1,0,1,0,0;
     0,0,1,1,0,1,0;
     0,0,0,1,1,0,1;
     1,0,0,0,1,1,0;
     0,1,0,0,0,1,1;
     1,0,1,0,0,0,1]

lemma fano_zeroOne : ZeroOne fano := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide
lemma fano_edgeCount : edgeCount fano = 21 := by decide
lemma fano_det : fano.det = 24 := by
  unfold fano
  eval_det

lemma fano_attains :
    (∀ i j, fano i j = 0 ∨ fano i j = 1) ∧
    (univ.filter (fun p : Fin 7 × Fin 7 => fano p.1 p.2 ≠ 0)).card = 21 ∧
    fano.det = 24 ∧ |fano.det| ^ 7 = (24 : ℤ) ^ 7 ∧
    ((fano.det : ℤ) : ℝ) = (24 : ℝ) ^ ((7 : ℝ) / 7) := by
  refine ⟨fano_zeroOne, fano_edgeCount, fano_det, ?_, ?_⟩ <;> rw [fano_det] <;> norm_num

#print axioms fano_attains
end SparseDet
```

### `SparseDeletion.lean`

```lean
import SparseStatement

open Matrix Finset
open scoped BigOperators
namespace SparseDet

lemma rowDegree_eq_zero_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    rowDegree A i = 0 ↔ ∀ j, A i j = 0 := by
  classical
  simp only [rowDegree, Finset.sum_eq_zero_iff, Finset.mem_univ, forall_const]
  simp

lemma rowDegree_pos_of_det_ne_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hdet : A.det ≠ 0) (i : Fin n) : 0 < rowDegree A i := by
  by_contra h
  have hz : rowDegree A i = 0 := by omega
  exact hdet (Matrix.det_eq_zero_of_row_eq_zero i ((rowDegree_eq_zero_iff A i).mp hz))

lemma degree_one_witness {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (h01 : ZeroOne A)
    (i : Fin n) (hi : rowDegree A i = 1) :
    ∃ j, A i j = 1 ∧ ∀ k, k ≠ j → A i k = 0 := by
  classical
  have hc : (univ.filter (fun j => A i j ≠ 0)).card = 1 := by
    simpa only [card_filter, rowDegree] using hi
  obtain ⟨j, hj⟩ := card_eq_one.mp hc
  have hmem : A i j ≠ 0 := by
    have hm : j ∈ univ.filter (fun j => A i j ≠ 0) := by rw [hj]; simp
    simpa using hm
  refine ⟨j, (h01 i j).resolve_left hmem, ?_⟩
  intro k hk
  by_contra hn
  have hm : k ∈ univ.filter (fun j => A i j ≠ 0) := by simp [hn]
  rw [hj] at hm
  exact hk (by simpa using hm)

lemma minor_zeroOne {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ)
    (h01 : ZeroOne A) (i j : Fin (n+1)) :
    ZeroOne (A.submatrix i.succAbove j.succAbove) := by
  intro k l
  exact h01 _ _

/-- Laplace expansion removes a row with its unique unit entry. -/
lemma abs_det_delete_row {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ)
    (i j : Fin (n+1)) (hij : A i j = 1)
    (hz : ∀ k, k ≠ j → A i k = 0) :
    |A.det| = |(A.submatrix i.succAbove j.succAbove).det| := by
  rw [Matrix.det_succ_row A i, Finset.sum_eq_single j]
  · simp [hij, abs_mul, abs_pow]
  · intro k _ hk
    simp [hz k hk]
  · simp

/-- Exact edge bookkeeping: a leaf row and its incident column remove precisely
    the column degree. There is no density hypothesis. -/
lemma edgeCount_delete_row {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ)
    (i j : Fin (n+1)) (hz : ∀ k, k ≠ j → A i k = 0) :
    edgeCount A = edgeCount (A.submatrix i.succAbove j.succAbove) + colDegree A j := by
  classical
  calc
    edgeCount A = ∑ l, ∑ k, if A k l ≠ 0 then 1 else 0 := by
      rw [edgeCount_eq_sum, Finset.sum_comm]
    _ = colDegree A j + ∑ l : Fin n, ∑ k, if A k (j.succAbove l) ≠ 0 then 1 else 0 :=
      Fin.sum_univ_succAbove _ j
    _ = colDegree A j + ∑ l : Fin n, ∑ k : Fin n,
        if A (i.succAbove k) (j.succAbove l) ≠ 0 then 1 else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro l _
      rw [Fin.sum_univ_succAbove _ i]
      simp [hz _ (Fin.succAbove_ne j l)]
    _ = edgeCount (A.submatrix i.succAbove j.succAbove) + colDegree A j := by
      rw [edgeCount_eq_sum, Finset.sum_comm]
      exact add_comm _ _

/-- The universal bound used by the induction; in particular no sparsity
    condition belongs in its induction hypothesis. -/
def PotentialBound (c d : ℝ) (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (|A.det| : ℝ) ≤ Real.exp (c * n + d * edgeCount A)

lemma potential_transpose (c d : ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    PotentialBound c d n A.transpose ↔ PotentialBound c d n A := by
  simp [PotentialBound, edgeCount_transpose]

lemma potential_leaf_step (c d : ℝ) (hd : 0 ≤ d) (hcd : 0 ≤ c + d)
    {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ)
    (i j : Fin (n+1)) (hij : A i j = 1)
    (hz : ∀ k, k ≠ j → A i k = 0)
    (hminor : PotentialBound c d n (A.submatrix i.succAbove j.succAbove)) :
    PotentialBound c d (n+1) A := by
  classical
  have hcol : 1 ≤ colDegree A j := by
    have he : (if A i j ≠ 0 then 1 else 0 : ℕ) ≤ colDegree A j :=
      Finset.single_le_sum (f := fun k => if A k j ≠ 0 then 1 else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simpa [hij] using he
  have hcount := edgeCount_delete_row A i j hz
  have hc : (edgeCount A : ℝ) =
      edgeCount (A.submatrix i.succAbove j.succAbove) + (colDegree A j : ℝ) := by
    exact_mod_cast hcount
  have ht : (1 : ℝ) ≤ colDegree A j := by exact_mod_cast hcol
  unfold PotentialBound at hminor ⊢
  have habs : |(A.det : ℝ)| = |((A.submatrix i.succAbove j.succAbove).det : ℝ)| := by
    exact_mod_cast abs_det_delete_row A i j hij hz
  rw [habs]
  refine hminor.trans (Real.exp_le_exp.mpr ?_)
  push_cast
  rw [hc]
  nlinarith [mul_nonneg hd (sub_nonneg.mpr ht)]

/-- Retires all low-degree deletion cases, reducing the conjecture to a
    nonsingular minimum-degree-two estimate for arbitrary density. -/
theorem potential_bound_of_min_degree (c d : ℝ) (hd : 0 ≤ d) (hcd : 0 ≤ c + d)
    (hcore : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), ZeroOne A → A.det ≠ 0 →
      (∀ i, 2 ≤ rowDegree A i) → (∀ j, 2 ≤ colDegree A j) → PotentialBound c d n A) :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), ZeroOne A → PotentialBound c d n A := by
  intro n
  induction n with
  | zero => intro A _; simp [PotentialBound, edgeCount, edges]
  | succ n ih =>
    intro A h01
    by_cases hdet : A.det = 0
    · simp only [PotentialBound, hdet, abs_zero, Int.cast_zero]
      exact (Real.exp_pos _).le
    by_cases hr : ∃ i, rowDegree A i = 1
    · obtain ⟨i, hi⟩ := hr
      obtain ⟨j, hij, hz⟩ := degree_one_witness A h01 i hi
      exact potential_leaf_step c d hd hcd A i j hij hz
        (ih _ (minor_zeroOne A h01 i j))
    by_cases hc : ∃ j, colDegree A j = 1
    · obtain ⟨j, hj⟩ := hc
      obtain ⟨i, hji, hz⟩ := degree_one_witness A.transpose (fun k l => h01 l k) j hj
      apply (potential_transpose c d A).mp
      exact potential_leaf_step c d hd hcd A.transpose j i hji hz
        (ih _ (minor_zeroOne A.transpose (fun k l => h01 l k) j i))
    apply hcore _ A h01 hdet
    · intro i
      have := rowDegree_pos_of_det_ne_zero A hdet i
      have := not_exists.mp hr i
      omega
    · intro j
      have ht : A.transpose.det ≠ 0 := by simpa using hdet
      have := rowDegree_pos_of_det_ne_zero A.transpose ht j
      have := not_exists.mp hc j
      rw [rowDegree_transpose] at *
      omega

#print axioms abs_det_delete_row
#print axioms edgeCount_delete_row
#print axioms potential_bound_of_min_degree
end SparseDet
```

### `SparseConstants.lean`

```lean
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace SparseDet
noncomputable def L : ℝ := 2 * Real.log 3 - Real.log 2
noncomputable def g : ℝ := (81 / 49) * (L - 7 / 2)
noncomputable def b : ℝ := 9 / 2 - 4 * g / 9
noncomputable def a : ℝ := -L - 1 + 4 * g / 81
noncomputable def eta : ℝ := (2 / 3) * Real.log 3 - 1 / 3 + g / 81
noncomputable def c : ℝ := (a + 5 / 2) / 2
noncomputable def d : ℝ := eta / 2

lemma log2_bounds : (69314 : ℝ) / 100000 < Real.log 2 ∧
    Real.log 2 < 69315 / 100000 := by
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
lemma log3_bounds : (109861 : ℝ) / 100000 < Real.log 3 ∧
    Real.log 3 < 109862 / 100000 := by
  constructor <;> linarith [Real.log_three_gt_d9, Real.log_three_lt_d9]
lemma g_bounds : -(33 : ℝ) / 10 < g ∧ g < -329 / 100 := by
  dsimp [g, L]
  constructor <;> linarith [log2_bounds.1, log2_bounds.2, log3_bounds.1, log3_bounds.2]
lemma g_neg : g < 0 := by linarith [g_bounds.2]
lemma d_pos : 0 < d := by
  dsimp [d, eta]
  linarith [g_bounds.1, log3_bounds.1]
lemma c_add_d_pos : 0 < c + d := by
  dsimp [c, a, d, eta, L]
  linarith [g_bounds.1, log2_bounds.1, log3_bounds.2]
lemma L_eq_log : L = Real.log (9 / 2) := by
  rw [Real.log_div (by norm_num : (9 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  have h9 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  simp [L, h9]
lemma c_add_three_d : c + 3 * d = Real.log 24 / 7 := by
  have h24 : Real.log (24 : ℝ) = 3 * Real.log 2 + Real.log 3 := by
    rw [show (24 : ℝ) = 2 ^ (3 : ℕ) * 3 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ^ (3 : ℕ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0),
      Real.log_pow]
    norm_num
  rw [h24]
  dsimp [c, a, d, eta, g, L]
  ring

noncomputable def H (k : ℝ) : ℝ :=
  (Real.log k - 5 / 4 - g / 36) / k + (9 / 4 - g / 18) / k^2 +
    3 * g / (4 * k^3) - g / (2 * k^4)
noncomputable def D : ℝ := 9 / 2 - g / 9
noncomputable def J (k : ℝ) : ℝ :=
  9 / 4 + g / 36 - Real.log k - D / k - 9 * g / (4 * k^2) + 2 * g / k^3
noncomputable def P (k : ℝ) : ℝ := k^3 - D*k^2 - (9*g/2)*k + 6*g

lemma H_three : 2 * H 3 = eta := by dsimp [H, eta]; ring
lemma H_two_lt_three : H 2 < H 3 := by
  dsimp [H]
  linarith [g_bounds.1, g_bounds.2, log2_bounds.2, log3_bounds.1]
lemma H_four_lt_three : H 4 < H 3 := by
  dsimp [H]
  rw [Real.log_four_eq]
  linarith [g_bounds.1, g_bounds.2, log2_bounds.2, log3_bounds.1]
lemma J_four_neg : J 4 < 0 := by
  dsimp [J, D]
  rw [Real.log_four_eq]
  linarith [g_bounds.1, log2_bounds.1]

lemma P_pos {k : ℝ} (hk : 4 ≤ k) : 0 < P k := by
  have hD : D < 6 := by dsimp [D]; linarith [g_bounds.1]
  have hp4 : 0 < -8 - 92*g/9 := by linarith [g_bounds.2]
  have hcoef : 0 < 48 - 8*D - 9*g/2 := by dsimp [D]; linarith [g_bounds.2]
  have hexp : P k = (k-4)^3 + (12-D)*(k-4)^2 +
      (48-8*D-9*g/2)*(k-4) + (-8-92*g/9) := by dsimp [P, D]; ring
  rw [hexp]
  have h1 : 0 ≤ (k-4)^3 := pow_nonneg (by linarith) _
  have h2 : 0 ≤ (12-D)*(k-4)^2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h3 : 0 ≤ (48-8*D-9*g/2)*(k-4) := mul_nonneg hcoef.le (by linarith)
  linarith

#print axioms g_bounds
#print axioms c_add_three_d
#print axioms H_four_lt_three
end SparseDet
```

### `SparseMonotonicity.lean`

```lean
import SparseConstants
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace SparseDet

lemma hasDerivAt_H {k : ℝ} (hk : 0 < k) : HasDerivAt H (J k / k^2) k := by
  have hn : k ≠ 0 := ne_of_gt hk
  have h := (((((Real.hasDerivAt_log hn).sub_const (5/4)).sub_const (g/36)).div
      (hasDerivAt_id k) hn).add
      ((hasDerivAt_const k (9/4-g/18)).div ((hasDerivAt_id k).pow 2) (pow_ne_zero 2 hn))).add
      ((hasDerivAt_const k (3*g)).div
        (((hasDerivAt_id k).pow 3).const_mul 4) (mul_ne_zero (by norm_num) (pow_ne_zero 3 hn)))
  have h' := h.sub ((hasDerivAt_const k g).div
      (((hasDerivAt_id k).pow 4).const_mul 2) (mul_ne_zero (by norm_num) (pow_ne_zero 4 hn)))
  convert h' using 1
  · funext x; rfl
  · dsimp [J, D]; norm_num; field_simp [hn]; ring

lemma hasDerivAt_J {k : ℝ} (hk : 0 < k) : HasDerivAt J (-P k / k^4) k := by
  have hn : k ≠ 0 := ne_of_gt hk
  have h := ((((hasDerivAt_const k (9/4+g/36)).sub (Real.hasDerivAt_log hn)).sub
      ((hasDerivAt_const k D).div (hasDerivAt_id k) hn)).sub
      ((hasDerivAt_const k (9*g)).div
        (((hasDerivAt_id k).pow 2).const_mul 4) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hn))))
  have h' := h.add ((hasDerivAt_const k (2*g)).div
      ((hasDerivAt_id k).pow 3) (pow_ne_zero 3 hn))
  convert h' using 1
  · funext x; rfl
  · dsimp [P]; norm_num; field_simp [hn]; ring

lemma J_strictAntiOn : StrictAntiOn J (Set.Ici 4) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici (4 : ℝ))
  · intro k hk
    exact (hasDerivAt_J (by have := hk; simp only [Set.mem_Ici] at this; linarith)).continuousAt.continuousWithinAt
  · intro k hk
    have hk' : 4 ≤ k := by simp only [interior_Ici, Set.mem_Ioi] at hk; linarith
    rw [(hasDerivAt_J (by linarith)).deriv]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (P_pos hk')) (pow_pos (by linarith) _)

lemma J_neg {k : ℝ} (hk : 4 ≤ k) : J k < 0 := by
  exact (J_strictAntiOn.antitoneOn (by simp) hk hk).trans_lt J_four_neg

/-- The scalar risk identified by the review: monotonicity on the whole ray. -/
lemma H_strictAntiOn : StrictAntiOn H (Set.Ici 4) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici (4 : ℝ))
  · intro k hk
    exact (hasDerivAt_H (by have := hk; simp only [Set.mem_Ici] at this; linarith)).continuousAt.continuousWithinAt
  · intro k hk
    have hk' : 4 ≤ k := by simp only [interior_Ici, Set.mem_Ioi] at hk; linarith
    rw [(hasDerivAt_H (by linarith)).deriv]
    exact div_neg_of_neg_of_pos (J_neg hk') (sq_pos_of_pos (by linarith))

lemma H_nat_le_three (k : ℕ) (hk : 2 ≤ k) : H k ≤ H 3 := by
  by_cases h2 : k = 2
  · subst k; exact H_two_lt_three.le
  by_cases h3 : k = 3
  · subst k; exact le_rfl
  have h4 : (4 : ℝ) ≤ k := by exact_mod_cast (show 4 ≤ k by omega)
  exact (H_strictAntiOn.antitoneOn (by simp) h4 h4).trans H_four_lt_three.le

#print axioms H_strictAntiOn
#print axioms H_nat_le_three
end SparseDet
```

### `SparseDegree.lean`

```lean
import SparseMonotonicity

namespace SparseDet
noncomputable def Q (x y : ℝ) : ℝ :=
  x*y*(x+y+2/3) - (x^3+y^3)/4 - (x^2+y^2)/6 - (x+y)/36 - x^2*y^2
noncomputable def F (r s : ℝ) : ℝ :=
  Real.log r / r + Real.log s / s + b / (r*s) + g * Q (1/r) (1/s)

lemma Q_centers (x y : ℝ) : Q x y =
    2*((x+1/3)/2)*x*y - ((x+1/3)/2)^2*x +
    2*((y+1/3)/2)*x*y - ((y+1/3)/2)^2*y - x^2*y^2 := by
  dsimp [Q]; ring

lemma F_diagonal {r : ℝ} (hr : r ≠ 0) : F r r / 2 - (5/4)/r = H r := by
  dsimp [F, H, Q, b]
  field_simp
  ring

lemma F_factor {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0) :
    (F r r + F s s)/2 - F r s =
      (1/r-1/s)^2 * (b/2+g*(1/r+1/s+1/3-(1/r+1/s)^2/2)) := by
  dsimp [F, Q]
  field_simp
  ring

lemma factor_bracket_pos (x y : ℝ) :
    0 < b/2 + g*(x+y+1/3-(x+y)^2/2) := by
  have ht : x+y+1/3-(x+y)^2/2 ≤ 5/6 := by nlinarith [sq_nonneg (x+y-1)]
  have hg := mul_le_mul_of_nonpos_left ht g_neg.le
  dsimp [b]
  linarith [g_bounds.1]

lemma F_le_diagonal {r s : ℝ} (hr : 2 ≤ r) (hs : 2 ≤ s) :
    F r s ≤ (F r r + F s s)/2 := by
  have hr0 : 0 < r := by linarith
  have hs0 : 0 < s := by linarith
  have hbr := factor_bracket_pos (1/r) (1/s)
  have heq := F_factor (ne_of_gt hr0) (ne_of_gt hs0)
  have := mul_nonneg (sq_nonneg (1/r-1/s)) hbr.le
  linarith

/-- The degree envelope is uniform in the two integer degrees; no cutoff. -/
lemma integer_degree_envelope (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) :
    F r s ≤ eta + (5/4) * (1/(r:ℝ)+1/(s:ℝ)) := by
  have hr' : (2:ℝ) ≤ r := by exact_mod_cast hr
  have hs' : (2:ℝ) ≤ s := by exact_mod_cast hs
  have hr0 : (r:ℝ) ≠ 0 := by linarith
  have hs0 : (s:ℝ) ≠ 0 := by linarith
  have hdiag := F_le_diagonal hr' hs'
  have hrr := F_diagonal hr0
  have hss := F_diagonal hs0
  have hR := H_nat_le_three r hr
  have hS := H_nat_le_three s hs
  have he := H_three
  rw [mul_add]
  simp only [mul_one_div]
  linarith

#print axioms integer_degree_envelope
end SparseDet
```

### `SparseMajorant.lean`

```lean
import SparseMonotonicity

namespace SparseDet
noncomputable def phi (x : ℝ) : ℝ := a+b*x+g*x^2-Real.log x
noncomputable def turningPoint : ℝ := -9/(4*g)

lemma turningPoint_bounds : (2:ℝ)/9 < turningPoint ∧ turningPoint < 1 := by
  have hg : 4*g < 0 := by linarith [g_neg]
  unfold turningPoint
  constructor
  · apply (lt_div_iff_of_neg hg).mpr
    linarith [g_bounds.1]
  · apply (div_lt_iff_of_neg hg).mpr
    linarith [g_bounds.2]

lemma phi_two_ninths : phi (2/9) = 0 := by
  have hl : Real.log ((2:ℝ)/9) = -L := by
    rw [Real.log_div (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (9:ℝ) ≠ 0)]
    rw [show (9:ℝ) = 3^(2:ℕ) by norm_num, Real.log_pow]
    dsimp [L]; norm_num
  dsimp [phi]
  rw [hl]
  dsimp [a, b]; ring
lemma phi_one : phi 1 = 0 := by
  dsimp [phi, a, b, g]
  rw [Real.log_one]
  ring

lemma hasDerivAt_phi {x : ℝ} (hx : 0 < x) :
    HasDerivAt phi (b+2*g*x-x⁻¹) x := by
  have h := ((((hasDerivAt_const x a).add ((hasDerivAt_id x).const_mul b)).add
    (((hasDerivAt_id x).pow 2).const_mul g)).sub (Real.hasDerivAt_log (ne_of_gt hx)))
  convert h using 1
  · funext t; rfl
  · norm_num; ring

lemma phi_deriv_factor {x : ℝ} (hx : x ≠ 0) :
    b+2*g*x-x⁻¹ = 2*g*(x-2/9)*(x-turningPoint)/x := by
  dsimp [b, turningPoint]
  field_simp [hx, ne_of_lt g_neg]
  ring

lemma phi_left : StrictAntiOn phi (Set.Ioc 0 (2/9)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc (0:ℝ) (2/9))
  · intro x hx
    exact (hasDerivAt_phi hx.1).continuousAt.continuousWithinAt
  · intro x hx
    simp only [interior_Ioc, Set.mem_Ioo] at hx
    rw [(hasDerivAt_phi hx.1).deriv, phi_deriv_factor (ne_of_gt hx.1)]
    have h1 : 0 < 2*g*(x-2/9) := mul_pos_of_neg_of_neg (by linarith [g_neg]) (by linarith)
    have h2 : x-turningPoint < 0 := by linarith [turningPoint_bounds.1]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h1 h2) hx.1

lemma phi_middle : StrictMonoOn phi (Set.Icc (2/9) turningPoint) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc ((2:ℝ)/9) turningPoint)
  · intro x hx
    exact (hasDerivAt_phi (by have := hx.1; linarith)).continuousAt.continuousWithinAt
  · intro x hx
    simp only [interior_Icc, Set.mem_Ioo] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    rw [(hasDerivAt_phi hx0).deriv, phi_deriv_factor (ne_of_gt hx0)]
    have h1 : 2*g*(x-2/9) < 0 := mul_neg_of_neg_of_pos (by linarith [g_neg]) (by linarith)
    have h2 : x-turningPoint < 0 := by linarith [hx.2]
    exact div_pos (mul_pos_of_neg_of_neg h1 h2) hx0

lemma phi_right : StrictAntiOn phi (Set.Icc turningPoint 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc turningPoint (1:ℝ))
  · intro x hx
    exact (hasDerivAt_phi (by have := hx.1; linarith [turningPoint_bounds.1])).continuousAt.continuousWithinAt
  · intro x hx
    simp only [interior_Icc, Set.mem_Ioo] at hx
    have hx0 : 0 < x := by linarith [hx.1, turningPoint_bounds.1]
    rw [(hasDerivAt_phi hx0).deriv, phi_deriv_factor (ne_of_gt hx0)]
    have h1 : 2*g*(x-2/9) < 0 := mul_neg_of_neg_of_pos (by linarith [g_neg])
      (by linarith [hx.1, turningPoint_bounds.1])
    have h2 : 0 < x-turningPoint := by linarith [hx.1]
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos h1 h2) hx0

lemma logarithmic_majorant (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    Real.log x ≤ a+b*x+g*x^2 := by
  have hphi : 0 ≤ phi x := by
    by_cases hl : x ≤ 2/9
    · have h := phi_left.antitoneOn ⟨hx, hl⟩ (by constructor <;> norm_num) hl
      rw [phi_two_ninths] at h
      exact h
    by_cases hm : x ≤ turningPoint
    · have h := phi_middle.monotoneOn (by constructor; rfl; exact turningPoint_bounds.1.le)
        ⟨le_of_not_ge hl, hm⟩ (le_of_not_ge hl)
      rw [phi_two_ninths] at h
      exact h
    · have h := phi_right.antitoneOn ⟨le_of_not_ge hm, hx1⟩
        ⟨turningPoint_bounds.2.le, le_rfl⟩ hx1
      rw [phi_one] at h
      exact h
  dsimp [phi] at hphi
  linarith

#print axioms logarithmic_majorant
end SparseDet
```

### `SparseSpectral.lean`

```lean
import SparseMajorant
import Mathlib.Analysis.Matrix.PosDef

open Matrix Finset Unitary
open scoped BigOperators
namespace SparseDet

lemma trace_square_eigenvalues {n : Type*} [Fintype n] [DecidableEq n]
    {K : Matrix n n ℝ} (hK : K.IsHermitian) :
    (K^2).trace = ∑ i, (hK.eigenvalues i)^2 := by
  have hp : K^2 = conjStarAlgAut ℝ _ hK.eigenvectorUnitary
      ((diagonal (RCLike.ofReal ∘ hK.eigenvalues))^2) := by
    rw [map_pow, ← hK.spectral_theorem]
  rw [hp, conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    Matrix.one_mul, Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp

lemma eigenvalue_le_one_of_quadratic {n : Type*} [Fintype n] [DecidableEq n]
    {K : Matrix n n ℝ} (hK : K.IsHermitian)
    (hcon : ∀ z : n → ℝ, z ⬝ᵥ (K *ᵥ z) ≤ z ⬝ᵥ z) (i : n) :
    hK.eigenvalues i ≤ 1 := by
  have hnorm : (⇑(hK.eigenvectorBasis i)) ⬝ᵥ (⇑(hK.eigenvectorBasis i)) = 1 := by
    have he := inner_self_eq_norm_sq_to_K (𝕜 := ℝ) (hK.eigenvectorBasis i)
    rw [EuclideanSpace.inner_eq_star_dotProduct] at he
    simpa [hK.eigenvectorBasis.orthonormal.1 i] using he
  calc
    hK.eigenvalues i = (⇑(hK.eigenvectorBasis i)) ⬝ᵥ (K *ᵥ ⇑(hK.eigenvectorBasis i)) := by
      simpa using hK.eigenvalues_eq i
    _ ≤ (⇑(hK.eigenvectorBasis i)) ⬝ᵥ (⇑(hK.eigenvectorBasis i)) := hcon _
    _ = 1 := hnorm

/-- Generic spectral summation. The scalar majorant is an explicit input, not
    an axiom. The next lemma supplies the proved scalar majorant. -/
lemma log_det_le_majorant {n : Type*} [Fintype n] [DecidableEq n]
    {K : Matrix n n ℝ} (hK : K.PosDef)
    (hcon : ∀ z : n → ℝ, z ⬝ᵥ (K *ᵥ z) ≤ z ⬝ᵥ z)
    (hmaj : ∀ x : ℝ, 0 < x → x ≤ 1 → Real.log x ≤ a+b*x+g*x^2) :
    Real.log K.det ≤ a * Fintype.card n + b * K.trace + g * (K^2).trace := by
  have hs : (∑ i, Real.log (hK.isHermitian.eigenvalues i)) ≤
      ∑ i, (a + b*hK.isHermitian.eigenvalues i + g*(hK.isHermitian.eigenvalues i)^2) := by
    apply Finset.sum_le_sum
    intro i _
    exact hmaj _ (hK.eigenvalues_pos i) (eigenvalue_le_one_of_quadratic hK.isHermitian hcon i)
  rw [hK.isHermitian.det_eq_prod_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [Real.log_prod (fun i _ => ne_of_gt (hK.eigenvalues_pos i))]
  rw [hK.isHermitian.trace_eq_sum_eigenvalues, trace_square_eigenvalues hK.isHermitian]
  simpa [Finset.sum_add_distrib, ← Finset.mul_sum, mul_comm] using hs

/-- The spectral estimate used in the manuscript, with no remaining scalar premise. -/
lemma log_det_le_quadratic {n : Type*} [Fintype n] [DecidableEq n]
    {K : Matrix n n ℝ} (hK : K.PosDef)
    (hcon : ∀ z : n → ℝ, z ⬝ᵥ (K *ᵥ z) ≤ z ⬝ᵥ z) :
    Real.log K.det ≤ a * Fintype.card n + b * K.trace + g * (K^2).trace :=
  log_det_le_majorant hK hcon logarithmic_majorant

#print axioms trace_square_eigenvalues
#print axioms eigenvalue_le_one_of_quadratic
#print axioms log_det_le_majorant
#print axioms log_det_le_quadratic
end SparseDet
```

### `SparseMoments.lean`

```lean
import SparseConstants
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

open Matrix Finset
open scoped BigOperators
namespace SparseDet

/-- A general nonnegative Gram-matrix moment inequality, before normalization.
    It keeps the diagonal exactly and drops only off-diagonal cross terms. -/
lemma gram_fourth_moment {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (B : Matrix n m ℝ) (hB : ∀ i j, 0 ≤ B i j) :
    (∑ i, (∑ j, B i j ^ 2)^2) + (∑ j, (∑ i, B i j ^ 2)^2) -
      (∑ i, ∑ j, B i j ^ 4) ≤ ((B * B.transpose)^2).trace := by
  have hpt : ∀ i k,
      (∑ j, B i j ^ 2 * B k j ^ 2) +
        (if k = i then (∑ j, B i j * B i j)^2 - (∑ j, B i j^4) else 0) ≤
        (∑ j, B i j * B k j)^2 := by
    intro i k
    by_cases hk : k = i
    · subst k
      simp only [ite_true]
      have he : (∑ j, B i j^2 * B i j^2) = ∑ j, B i j^4 := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [he]
      linarith
    · simp only [hk, ite_false, add_zero]
      have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := (univ : Finset m))
        (f := fun j => B i j * B k j) (fun j _ => mul_nonneg (hB i j) (hB k j))
      simpa only [mul_pow] using h
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset n)) =>
    Finset.sum_le_sum (fun k (_ : k ∈ (univ : Finset n)) => hpt i k))
  have hw : (∑ i, ∑ k, ∑ j, B i j^2 * B k j^2) = ∑ j, (∑ i, B i j^2)^2 := by
    calc
      _ = ∑ i, ∑ j, ∑ k, B i j^2 * B k j^2 := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = ∑ j, ∑ i, ∑ k, B i j^2 * B k j^2 := Finset.sum_comm
      _ = _ := by
        simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        ring
  have htr : ((B * B.transpose)^2).trace = ∑ i, ∑ k, (∑ j, B i j * B k j)^2 := by
    simp only [pow_two, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_sub_distrib] at hs
  rw [hw, ← htr] at hs
  have hdiag : (∑ i, (∑ j, B i j * B i j)^2) = ∑ i, (∑ j, B i j^2)^2 := by
    simp only [pow_two]
  rw [hdiag] at hs
  linarith

/-- Each completed square has a degree-dependent center in the application. -/
lemma sum_square_completion {n : Type*} [Fintype n] (v u : n → ℝ) :
    (∑ i, (2*u i*v i - (u i)^2)) ≤ ∑ i, (v i)^2 := by
  apply Finset.sum_le_sum
  intro i _
  nlinarith [sq_nonneg (v i-u i)]

#print axioms gram_fourth_moment
#print axioms sum_square_completion
end SparseDet
```

### `SparseNormalization.lean`

```lean
import SparseDeletion
import SparseMoments
import Mathlib.Analysis.Matrix.PosDef

open Matrix Finset
open scoped BigOperators
namespace SparseDet
noncomputable def realMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  A.map (Int.castRingHom ℝ)
noncomputable def rowWeight {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : ℝ :=
  (Real.sqrt (rowDegree A i))⁻¹
noncomputable def colWeight {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) : ℝ :=
  (Real.sqrt (colDegree A j))⁻¹
noncomputable def normalized {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal (rowWeight A) * realMatrix A * diagonal (colWeight A)
noncomputable def gram {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  normalized A * (normalized A).transpose

lemma normalized_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    normalized A i j = rowWeight A i * (A i j : ℝ) * colWeight A j := by
  simp [normalized, Matrix.mul_diagonal, Matrix.diagonal_mul, realMatrix]
lemma normalized_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (h01 : ZeroOne A)
    (i j : Fin n) : 0 ≤ normalized A i j := by
  rw [normalized_apply]
  have ha : 0 ≤ (A i j : ℝ) := by rcases h01 i j with h | h <;> rw [h] <;> norm_num
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) ha)
    (inv_nonneg.mpr (Real.sqrt_nonneg _))

lemma normalized_square {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (h01 : ZeroOne A)
    (i j : Fin n) : (normalized A i j)^2 =
    if A i j ≠ 0 then 1/((rowDegree A i : ℝ)*(colDegree A j : ℝ)) else 0 := by
  rw [normalized_apply]
  rcases h01 i j with h | h
  · simp [h]
  · simp only [h, Int.cast_one, mul_one]
    rw [mul_pow]
    simp only [rowWeight, colWeight, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp [one_div, mul_comm]

lemma gram_isHermitian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : (gram A).IsHermitian := by
  simpa only [gram, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_mul_conjTranspose_self (normalized A)

lemma gram_fourth_moment_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (h01 : ZeroOne A) :
    (∑ i, (∑ j, normalized A i j ^ 2)^2) +
    (∑ j, (∑ i, normalized A i j ^ 2)^2) -
    (∑ i, ∑ j, normalized A i j ^ 4) ≤ ((gram A)^2).trace :=
  gram_fourth_moment _ (normalized_nonneg A h01)

#print axioms normalized_square
#print axioms gram_fourth_moment_bound
end SparseDet
```

### `SparseEdges.lean`

```lean
import SparseNormalization
import SparseDegree

open Matrix Finset
open scoped BigOperators
namespace SparseDet

noncomputable def edgeSum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (f : Fin n → Fin n → ℝ) : ℝ := ∑ i, ∑ j, if A i j ≠ 0 then f i j else 0

lemma edgeSum_add {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (f h : Fin n → Fin n → ℝ) :
    edgeSum A (fun i j => f i j + h i j) = edgeSum A f + edgeSum A h := by
  simp only [edgeSum, ← sum_add_distrib]
  apply sum_congr rfl; intro i _
  apply sum_congr rfl; intro j _
  split_ifs <;> simp

lemma edgeSum_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (t : ℝ)
    (f : Fin n → Fin n → ℝ) :
    edgeSum A (fun i j => t * f i j) = t * edgeSum A f := by
  simp only [edgeSum, mul_sum]
  apply sum_congr rfl; intro i _
  apply sum_congr rfl; intro j _
  split_ifs <;> simp

lemma edgeSum_mono {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (f h : Fin n → Fin n → ℝ) (hf : ∀ i j, f i j ≤ h i j) : edgeSum A f ≤ edgeSum A h := by
  apply sum_le_sum; intro i _
  apply sum_le_sum; intro j _
  split_ifs; exact hf i j; exact le_rfl

lemma row_sum_const {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) (t : ℝ) :
    (∑ j, if A i j ≠ 0 then t else 0) = (rowDegree A i : ℝ) * t := by
  have h : (rowDegree A i : ℝ) = ∑ j, if A i j ≠ 0 then (1:ℝ) else 0 := by
    simp [rowDegree, Nat.cast_sum, Nat.cast_ite]
  rw [h, sum_mul]
  apply sum_congr rfl; intro j _; split_ifs <;> simp

lemma col_sum_const {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) (t : ℝ) :
    (∑ i, if A i j ≠ 0 then t else 0) = (colDegree A j : ℝ) * t :=
  row_sum_const A.transpose j t

lemma edgeSum_row {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (f : Fin n → ℝ) :
    edgeSum A (fun i _ => f i) = ∑ i, (rowDegree A i : ℝ) * f i := by
  simp only [edgeSum, row_sum_const]

lemma edgeSum_col {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (f : Fin n → ℝ) :
    edgeSum A (fun _ j => f j) = ∑ j, (colDegree A j : ℝ) * f j := by
  rw [edgeSum, sum_comm]; simp only [col_sum_const]

lemma edgeSum_const {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (t : ℝ) :
    edgeSum A (fun _ _ => t) = (edgeCount A : ℝ) * t := by
  rw [edgeSum_row, ← sum_mul]
  congr 1
  simp [rowDegree, edgeCount_eq_sum, Nat.cast_sum, Nat.cast_ite]

lemma edgeSum_row_div {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hr : ∀ i, rowDegree A i ≠ 0) (f : Fin n → ℝ) :
    edgeSum A (fun i _ => f i / rowDegree A i) = ∑ i, f i := by
  rw [edgeSum_row]
  apply sum_congr rfl; intro i _
  have hi : (rowDegree A i : ℝ) ≠ 0 := by exact_mod_cast hr i
  field_simp

lemma edgeSum_col_div {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hc : ∀ j, colDegree A j ≠ 0) (f : Fin n → ℝ) :
    edgeSum A (fun _ j => f j / colDegree A j) = ∑ j, f j := by
  rw [edgeSum_col]
  apply sum_congr rfl; intro j _
  have hj : (colDegree A j : ℝ) ≠ 0 := by exact_mod_cast hc j
  field_simp

lemma edgeSum_recip {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hr : ∀ i, rowDegree A i ≠ 0) (hc : ∀ j, colDegree A j ≠ 0) :
    edgeSum A (fun i j => 1/(rowDegree A i : ℝ) + 1/(colDegree A j : ℝ)) = 2*n := by
  rw [edgeSum_add, edgeSum_row_div A hr, edgeSum_col_div A hc]
  simp; ring

lemma degree_edge_envelope {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hr : ∀ i, 2 ≤ rowDegree A i) (hc : ∀ j, 2 ≤ colDegree A j) :
    edgeSum A (fun i j => F (rowDegree A i) (colDegree A j)) ≤
      eta * edgeCount A + (5/2) * n := by
  have he := edgeSum_mono A _ _ (fun i j => integer_degree_envelope _ _ (hr i) (hc j))
  rw [edgeSum_add, edgeSum_const, edgeSum_smul,
    edgeSum_recip A (fun i => by have := hr i; omega) (fun j => by have := hc j; omega)] at he
  nlinarith
end SparseDet
```

### `SparseGramDet.lean`

```lean
import SparseNormalization
import Mathlib.Algebra.Order.Star.Real

open Matrix Finset
open scoped BigOperators
namespace SparseDet

lemma colDegree_pos_of_det_ne_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hdet : A.det ≠ 0) (j : Fin n) : 0 < colDegree A j := by
  exact rowDegree_pos_of_det_ne_zero A.transpose (by simpa using hdet) j

lemma realMatrix_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    (realMatrix A).det = (A.det : ℝ) := by
  exact (Int.castRingHom ℝ).map_det A |>.symm

lemma normalized_det_ne_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hdet : A.det ≠ 0) : (normalized A).det ≠ 0 := by
  rw [normalized, det_mul, det_mul, det_diagonal, det_diagonal, realMatrix_det]
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply prod_ne_zero_iff.mpr; intro i _
      exact inv_ne_zero (Real.sqrt_ne_zero'.mpr (by exact_mod_cast rowDegree_pos_of_det_ne_zero A hdet i))
    · exact_mod_cast hdet
  · apply prod_ne_zero_iff.mpr; intro j _
    exact inv_ne_zero (Real.sqrt_ne_zero'.mpr (by exact_mod_cast colDegree_pos_of_det_ne_zero A hdet j))

lemma gram_posDef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hdet : A.det ≠ 0) : (gram A).PosDef := by
  have hu : IsUnit (normalized A) := ((normalized A).isUnit_iff_isUnit_det).mpr
    (isUnit_iff_ne_zero.mpr (normalized_det_ne_zero A hdet))
  simpa only [gram, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.mul_conjTranspose_self (normalized A) (Matrix.vecMul_injective_iff_isUnit.mpr hu)

lemma log_gram_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hdet : A.det ≠ 0) :
    2 * Real.log |(A.det : ℝ)| =
      (∑ i, Real.log (rowDegree A i)) +
      (∑ j, Real.log (colDegree A j)) + Real.log (gram A).det := by
  have hr : ∀ i ∈ (univ : Finset (Fin n)), rowWeight A i ≠ 0 := by
    intro i _; exact inv_ne_zero (Real.sqrt_ne_zero'.mpr
      (by exact_mod_cast rowDegree_pos_of_det_ne_zero A hdet i))
  have hc : ∀ j ∈ (univ : Finset (Fin n)), colWeight A j ≠ 0 := by
    intro j _; exact inv_ne_zero (Real.sqrt_ne_zero'.mpr
      (by exact_mod_cast colDegree_pos_of_det_ne_zero A hdet j))
  have hA : (A.det : ℝ) ≠ 0 := by exact_mod_cast hdet
  have hB := normalized_det_ne_zero A hdet
  have hlog : Real.log (gram A).det =
      2 * (∑ i, Real.log (rowWeight A i)) + 2 * Real.log (A.det : ℝ) +
      2 * (∑ j, Real.log (colWeight A j)) := by
    rw [gram, det_mul, det_transpose, Real.log_mul hB hB, normalized,
      det_mul, det_mul, det_diagonal, det_diagonal,
      Real.log_mul (mul_ne_zero (prod_ne_zero_iff.mpr hr) (by rwa [realMatrix_det]))
        (prod_ne_zero_iff.mpr hc),
      Real.log_mul (prod_ne_zero_iff.mpr hr) (by rwa [realMatrix_det]),
      realMatrix_det, Real.log_prod hr, Real.log_prod hc]
    ring
  have hrlog : (∑ i, Real.log (rowWeight A i)) = -(∑ i, Real.log (rowDegree A i)) / 2 := by
    simp only [rowWeight, Real.log_inv, Real.log_sqrt (Nat.cast_nonneg _), sum_neg_distrib,
      ← sum_div, neg_div]
  have hclog : (∑ j, Real.log (colWeight A j)) = -(∑ j, Real.log (colDegree A j)) / 2 := by
    simp only [colWeight, Real.log_inv, Real.log_sqrt (Nat.cast_nonneg _), sum_neg_distrib,
      ← sum_div, neg_div]
  rw [hrlog, hclog, ← Real.log_abs (A.det : ℝ)] at hlog
  linarith
end SparseDet
```

### `SparseContraction.lean`

```lean
import SparseEdges

open Matrix Finset
open scoped BigOperators
namespace SparseDet

lemma indicator_cauchy {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (v : ι → ℝ) :
    (∑ i, if p i then v i else 0)^2 ≤
      (∑ i, if p i then (1:ℝ) else 0) * (∑ i, if p i then v i ^ 2 else 0) := by
  have hm (i : ι) : (if p i then (1:ℝ) else 0) * (if p i then v i else 0) =
      (if p i then v i else 0) := by split_ifs <;> simp
  simpa only [hm, ite_pow, one_pow, zero_pow (by decide : 2 ≠ 0)] using
    (sum_mul_sq_le_sq_mul_sq univ (fun i => if p i then (1:ℝ) else 0)
      (fun i => if p i then v i else 0))

lemma transpose_mulVec_normalized {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (h01 : ZeroOne A) (z : Fin n → ℝ) (j : Fin n) :
    ((normalized A).transpose *ᵥ z) j = colWeight A j *
      ∑ i, if A i j ≠ 0 then rowWeight A i * z i else 0 := by
  simp only [mulVec, dotProduct, transpose_apply, normalized_apply, mul_sum]
  apply sum_congr rfl; intro i _
  rcases h01 i j with h | h <;> simp [h]; ring

lemma normalized_transpose_contracts {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (h01 : ZeroOne A) (hr : ∀ i, rowDegree A i ≠ 0) (hc : ∀ j, colDegree A j ≠ 0)
    (z : Fin n → ℝ) :
    (∑ j, (((normalized A).transpose *ᵥ z) j)^2) ≤ ∑ i, (z i)^2 := by
  have hcol (j : Fin n) : (((normalized A).transpose *ᵥ z) j)^2 ≤
      ∑ i, if A i j ≠ 0 then (z i)^2 / rowDegree A i else 0 := by
    have hh := indicator_cauchy (fun i => A i j ≠ 0) (fun i => rowWeight A i * z i)
    have hs : (∑ i, if A i j ≠ 0 then (1:ℝ) else 0) = (colDegree A j : ℝ) := by
      simpa using col_sum_const A j 1
    rw [hs] at hh
    have hw : colWeight A j ^ 2 * (colDegree A j : ℝ) = 1 := by
      have hj : (colDegree A j : ℝ) ≠ 0 := by exact_mod_cast hc j
      simp only [colWeight, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      exact inv_mul_cancel₀ hj
    have h := mul_le_mul_of_nonneg_left hh (sq_nonneg (colWeight A j))
    rw [← mul_assoc, hw, one_mul] at h
    rw [transpose_mulVec_normalized A h01 z j, mul_pow]
    refine h.trans_eq ?_
    apply sum_congr rfl; intro i _
    split_ifs
    · simp only [mul_pow, rowWeight, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      ring
    · rfl
  calc
    _ ≤ ∑ j, ∑ i, if A i j ≠ 0 then (z i)^2 / rowDegree A i else 0 :=
      sum_le_sum (fun j _ => hcol j)
    _ = edgeSum A (fun i _ => (z i)^2 / rowDegree A i) := sum_comm
    _ = _ := edgeSum_row_div A hr _

lemma gram_contracts {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (h01 : ZeroOne A) (hr : ∀ i, 2 ≤ rowDegree A i) (hc : ∀ j, 2 ≤ colDegree A j) :
    ∀ z : Fin n → ℝ, z ⬝ᵥ (gram A *ᵥ z) ≤ z ⬝ᵥ z := by
  intro z
  have h := normalized_transpose_contracts A h01 (fun i => by have := hr i; omega)
    (fun j => by have := hc j; omega) z
  rw [gram, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  simpa only [dotProduct, pow_two] using h
end SparseDet
```

### `SparseTrace.lean`

```lean
import SparseEdges

open Matrix Finset
open scoped BigOperators
namespace SparseDet

lemma edgeSum_sub {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (f h : Fin n → Fin n → ℝ) :
    edgeSum A (fun i j => f i j - h i j) = edgeSum A f - edgeSum A h := by
  simp only [edgeSum, ← sum_sub_distrib]
  apply sum_congr rfl; intro i _
  apply sum_congr rfl; intro j _
  split_ifs <;> simp

lemma trace_gram {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (h01 : ZeroOne A) :
    (gram A).trace = edgeSum A (fun i j => 1/((rowDegree A i : ℝ)*(colDegree A j : ℝ))) := by
  simp only [gram, trace, diag_apply, mul_apply, transpose_apply, edgeSum]
  apply sum_congr rfl; intro i _
  apply sum_congr rfl; intro j _
  rw [← pow_two, normalized_square A h01]

lemma edgeSum_weight_row {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (h01 : ZeroOne A)
    (t : Fin n → ℝ) :
    edgeSum A (fun i j => t i / ((rowDegree A i : ℝ)*(colDegree A j : ℝ))) =
      ∑ i, t i * (∑ j, normalized A i j ^ 2) := by
  simp only [edgeSum, mul_sum, normalized_square A h01]
  apply sum_congr rfl; intro i _
  apply sum_congr rfl; intro j _
  split_ifs <;> simp; ring

lemma edgeSum_weight_col {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (h01 : ZeroOne A)
    (t : Fin n → ℝ) :
    edgeSum A (fun i j => t j / ((rowDegree A i : ℝ)*(colDegree A j : ℝ))) =
      ∑ j, t j * (∑ i, normalized A i j ^ 2) := by
  rw [edgeSum, sum_comm]
  simp only [mul_sum, normalized_square A h01]
  apply sum_congr rfl; intro j _
  apply sum_congr rfl; intro i _
  split_ifs <;> simp; ring

lemma edgeSum_fourth {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (h01 : ZeroOne A) :
    edgeSum A (fun i j => (1/((rowDegree A i : ℝ)*(colDegree A j : ℝ)))^2) =
      ∑ i, ∑ j, normalized A i j ^ 4 := by
  apply sum_congr rfl; intro i _
  apply sum_congr rfl; intro j _
  rw [show normalized A i j ^ 4 = (normalized A i j ^ 2)^2 by ring,
    normalized_square A h01]
  split_ifs <;> simp

lemma edgeSum_centers {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (h01 : ZeroOne A)
    (hr : ∀ i, rowDegree A i ≠ 0) (hc : ∀ j, colDegree A j ≠ 0)
    (u v : Fin n → ℝ) :
    edgeSum A (fun i j =>
      (2*u i/((rowDegree A i : ℝ)*(colDegree A j : ℝ)) - (u i)^2/rowDegree A i) +
      (2*v j/((rowDegree A i : ℝ)*(colDegree A j : ℝ)) - (v j)^2/colDegree A j) -
      (1/((rowDegree A i : ℝ)*(colDegree A j : ℝ)))^2) =
    (∑ i, (2*u i*(∑ j, normalized A i j ^ 2) - (u i)^2)) +
    (∑ j, (2*v j*(∑ i, normalized A i j ^ 2) - (v j)^2)) -
    (∑ i, ∑ j, normalized A i j ^ 4) := by
  rw [edgeSum_sub, edgeSum_add, edgeSum_sub, edgeSum_sub,
    edgeSum_weight_row A h01, edgeSum_weight_col A h01,
    edgeSum_row_div A hr, edgeSum_col_div A hc, edgeSum_fourth A h01,
    sum_sub_distrib, sum_sub_distrib]

lemma trace_gram_square_lower {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (h01 : ZeroOne A) (hr : ∀ i, 2 ≤ rowDegree A i) (hc : ∀ j, 2 ≤ colDegree A j) :
    edgeSum A (fun i j => Q (1/(rowDegree A i : ℝ)) (1/(colDegree A j : ℝ))) ≤
      ((gram A)^2).trace := by
  let u : Fin n → ℝ := fun i => (1/(rowDegree A i : ℝ)+1/3)/2
  let v : Fin n → ℝ := fun j => (1/(colDegree A j : ℝ)+1/3)/2
  have heq : edgeSum A (fun i j => Q (1/(rowDegree A i : ℝ)) (1/(colDegree A j : ℝ))) =
      (∑ i, (2*u i*(∑ j, normalized A i j ^ 2) - (u i)^2)) +
      (∑ j, (2*v j*(∑ i, normalized A i j ^ 2) - (v j)^2)) -
      (∑ i, ∑ j, normalized A i j ^ 4) := by
    rw [← edgeSum_centers A h01 (fun i => by have := hr i; omega)
      (fun j => by have := hc j; omega) u v]
    congr 1; funext i j
    rw [Q_centers]
    dsimp [u,v]; ring
  rw [heq]
  have hrow := sum_square_completion (fun i => ∑ j, normalized A i j ^ 2) u
  have hcol := sum_square_completion (fun j => ∑ i, normalized A i j ^ 2) v
  have hm := gram_fourth_moment_bound A h01
  linarith
end SparseDet
```

### `SparseAssembly.lean`

```lean
import SparseDeletion
import SparseConstants

namespace SparseDet

/-- The sole remaining matrix estimate. This is a proposition, not an axiom
    or an assumed theorem in the final endpoint. -/
def MinDegreeEstimate : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), ZeroOne A → A.det ≠ 0 →
    (∀ i, 2 ≤ rowDegree A i) → (∀ j, 2 ≤ colDegree A j) → PotentialBound c d n A

lemma universal_of_min_degree (hcore : MinDegreeEstimate) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (h01 : ZeroOne A) : PotentialBound c d n A :=
  potential_bound_of_min_degree c d d_pos.le c_add_d_pos.le hcore n A h01

lemma absolute_real_of_min_degree (hcore : MinDegreeEstimate) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (h01 : ZeroOne A)
    (hsparse : edgeCount A ≤ 3*n) :
    |(A.det : ℝ)| ≤ (24:ℝ)^((n:ℝ)/7) := by
  have hb := universal_of_min_degree hcore n A h01
  have hm : (edgeCount A : ℝ) ≤ 3*(n:ℝ) := by exact_mod_cast hsparse
  have hpot : c*(n:ℝ)+d*(edgeCount A:ℝ) ≤ Real.log 24*((n:ℝ)/7) := by
    have hh : (c+3*d)*(n:ℝ) = Real.log 24*((n:ℝ)/7) := by rw [c_add_three_d]; ring
    rw [← hh]
    nlinarith [mul_nonneg d_pos.le (sub_nonneg.mpr hm)]
  change |(A.det : ℝ)| ≤ _ at hb
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 24)]
  exact hb.trans (Real.exp_le_exp.mpr hpot)

/-- Conditional assembly only. The unqualified integer companion is not yet
    declared, because `MinDegreeEstimate` is not yet proved. -/
theorem integer_bound_of_min_degree (hcore : MinDegreeEstimate) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hsparse : (Finset.univ.filter (fun p : Fin n × Fin n => A p.1 p.2 ≠ 0)).card ≤ 3*n) :
    |A.det|^7 ≤ (24:ℤ)^n := by
  have h := pow_le_pow_left₀ (abs_nonneg (A.det:ℝ))
    (absolute_real_of_min_degree hcore n A h01 hsparse) 7
  have hid : ((24:ℝ)^((n:ℝ)/7))^(7:ℕ) = (24:ℝ)^n := by
    calc
      _ = (24:ℝ)^(((n:ℝ)/7)*7) := by
        simpa only [Nat.cast_ofNat] using
          (Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 24) ((n:ℝ)/7) 7).symm
      _ = (24:ℝ)^(n:ℝ) := by congr 1; ring
      _ = (24:ℝ)^n := Real.rpow_natCast _ _
  rw [hid] at h
  exact_mod_cast h

/-- Exact printed conclusion and hypotheses, with the one open matrix lemma
    displayed explicitly as an additional premise. This is NOT the headline. -/
theorem printed_bound_of_min_degree (hcore : MinDegreeEstimate) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hsparse : (Finset.univ.filter (fun p : Fin n × Fin n => A p.1 p.2 ≠ 0)).card ≤ 3*n) :
    ((A.det:ℤ):ℝ) ≤ (24:ℝ)^((n:ℝ)/7) :=
  real_bound_of_integer_bound n A.det (integer_bound_of_min_degree hcore n A h01 hsparse)

#print MinDegreeEstimate
#print axioms integer_bound_of_min_degree
#print axioms printed_bound_of_min_degree
end SparseDet
```

### `SparseFinal.lean`

```lean
import SparseAssembly
import SparseGramDet
import SparseContraction
import SparseTrace
import SparseSpectral

open Matrix Finset
open scoped BigOperators
namespace SparseDet

lemma edgeSum_F {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (h01 : ZeroOne A)
    (hr : ∀ i, rowDegree A i ≠ 0) (hc : ∀ j, colDegree A j ≠ 0) :
    edgeSum A (fun i j => F (rowDegree A i) (colDegree A j)) =
      (∑ i, Real.log (rowDegree A i)) + (∑ j, Real.log (colDegree A j)) +
      b * (gram A).trace +
      g * edgeSum A (fun i j => Q (1/(rowDegree A i : ℝ)) (1/(colDegree A j : ℝ))) := by
  have he : (fun i j => F (rowDegree A i) (colDegree A j)) =
      (fun i j => Real.log (rowDegree A i) / rowDegree A i +
        Real.log (colDegree A j) / colDegree A j +
        b * (1/((rowDegree A i : ℝ)*(colDegree A j : ℝ))) +
        g * Q (1/(rowDegree A i : ℝ)) (1/(colDegree A j : ℝ))) := by
    funext i j; dsimp [F]; ring
  rw [he, edgeSum_add, edgeSum_add, edgeSum_add, edgeSum_smul, edgeSum_smul,
    edgeSum_row_div A hr, edgeSum_col_div A hc, ← trace_gram A h01]

theorem min_degree_estimate : MinDegreeEstimate := by
  intro n A h01 hdet hr hc
  have hpos := gram_posDef A hdet
  have hspectral := log_det_le_quadratic hpos (gram_contracts A h01 hr hc)
  simp only [Fintype.card_fin] at hspectral
  have hmoment := trace_gram_square_lower A h01 hr hc
  have hneg := mul_le_mul_of_nonpos_left hmoment g_neg.le
  have hdetlog := log_gram_det A hdet
  have henv := degree_edge_envelope A hr hc
  rw [edgeSum_F A h01 (fun i => by have := hr i; omega)
    (fun j => by have := hc j; omega)] at henv
  have hlog : Real.log |(A.det : ℝ)| ≤ c*n+d*edgeCount A := by
    dsimp [c,d]
    linarith
  have hA : (A.det : ℝ) ≠ 0 := by exact_mod_cast hdet
  exact (Real.log_le_iff_le_exp (abs_pos.mpr hA)).mp hlog

/-- Uniform potential estimate, without a sparsity restriction. -/
theorem universal_potential (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (h01 : ZeroOne A) : PotentialBound c d n A :=
  universal_of_min_degree min_degree_estimate n A h01

theorem mathdb_348549_integer (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hsparse : (Finset.univ.filter (fun p : Fin n × Fin n => A p.1 p.2 ≠ 0)).card ≤ 3*n) :
    |A.det|^7 ≤ (24:ℤ)^n :=
  integer_bound_of_min_degree min_degree_estimate n A h01 hsparse

theorem mathdb_348549 (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hsparse : (Finset.univ.filter (fun p : Fin n × Fin n => A p.1 p.2 ≠ 0)).card ≤ 3 * n) :
    ((A.det : ℤ) : ℝ) ≤ (24 : ℝ) ^ ((n : ℝ) / 7) :=
  real_bound_of_integer_bound n A.det (mathdb_348549_integer n A h01 hsparse)

#print axioms mathdb_348549_integer
#print axioms mathdb_348549
#print mathdb_348549_integer
#print mathdb_348549

-- The exact endpoint propositions are checked by definitional equality.
example : PrintedConjecture := mathdb_348549
example : IntegerConjecture := mathdb_348549_integer
end SparseDet
```

### `SparseAudit.lean`

```lean
import SparseStatement
import SparseSanity
import SparseDeletion
import SparseConstants
import SparseMonotonicity
import SparseDegree
import SparseMajorant
import SparseSpectral
import SparseMoments
import SparseNormalization
import SparseAssembly

#eval Lean.versionString
#check @SparseDet.edgeCount_eq_sum
#print axioms SparseDet.edgeCount_eq_sum
#check @SparseDet.edgeCount_transpose
#print axioms SparseDet.edgeCount_transpose
#check @SparseDet.rowDegree_transpose
#print axioms SparseDet.rowDegree_transpose
#check @SparseDet.colDegree_transpose
#print axioms SparseDet.colDegree_transpose
#check @SparseDet.identity_zeroOne
#print axioms SparseDet.identity_zeroOne
#check @SparseDet.identity_edgeCount
#print axioms SparseDet.identity_edgeCount
#check @SparseDet.identity_satisfies
#print axioms SparseDet.identity_satisfies
#check @SparseDet.order_zero
#print axioms SparseDet.order_zero
#check @SparseDet.real_bound_of_integer_bound
#print axioms SparseDet.real_bound_of_integer_bound
#check @SparseDet.fano_zeroOne
#print axioms SparseDet.fano_zeroOne
#check @SparseDet.fano_edgeCount
#print axioms SparseDet.fano_edgeCount
#check @SparseDet.fano_det
#print axioms SparseDet.fano_det
#check @SparseDet.fano_attains
#print axioms SparseDet.fano_attains
#check @SparseDet.rowDegree_eq_zero_iff
#print axioms SparseDet.rowDegree_eq_zero_iff
#check @SparseDet.rowDegree_pos_of_det_ne_zero
#print axioms SparseDet.rowDegree_pos_of_det_ne_zero
#check @SparseDet.degree_one_witness
#print axioms SparseDet.degree_one_witness
#check @SparseDet.minor_zeroOne
#print axioms SparseDet.minor_zeroOne
#check @SparseDet.abs_det_delete_row
#print axioms SparseDet.abs_det_delete_row
#check @SparseDet.edgeCount_delete_row
#print axioms SparseDet.edgeCount_delete_row
#check @SparseDet.potential_transpose
#print axioms SparseDet.potential_transpose
#check @SparseDet.potential_leaf_step
#print axioms SparseDet.potential_leaf_step
#check @SparseDet.potential_bound_of_min_degree
#print axioms SparseDet.potential_bound_of_min_degree
#check @SparseDet.log2_bounds
#print axioms SparseDet.log2_bounds
#check @SparseDet.log3_bounds
#print axioms SparseDet.log3_bounds
#check @SparseDet.g_bounds
#print axioms SparseDet.g_bounds
#check @SparseDet.g_neg
#print axioms SparseDet.g_neg
#check @SparseDet.d_pos
#print axioms SparseDet.d_pos
#check @SparseDet.c_add_d_pos
#print axioms SparseDet.c_add_d_pos
#check @SparseDet.L_eq_log
#print axioms SparseDet.L_eq_log
#check @SparseDet.c_add_three_d
#print axioms SparseDet.c_add_three_d
#check @SparseDet.H_three
#print axioms SparseDet.H_three
#check @SparseDet.H_two_lt_three
#print axioms SparseDet.H_two_lt_three
#check @SparseDet.H_four_lt_three
#print axioms SparseDet.H_four_lt_three
#check @SparseDet.J_four_neg
#print axioms SparseDet.J_four_neg
#check @SparseDet.P_pos
#print axioms SparseDet.P_pos
#check @SparseDet.hasDerivAt_H
#print axioms SparseDet.hasDerivAt_H
#check @SparseDet.hasDerivAt_J
#print axioms SparseDet.hasDerivAt_J
#check @SparseDet.J_strictAntiOn
#print axioms SparseDet.J_strictAntiOn
#check @SparseDet.J_neg
#print axioms SparseDet.J_neg
#check @SparseDet.H_strictAntiOn
#print axioms SparseDet.H_strictAntiOn
#check @SparseDet.H_nat_le_three
#print axioms SparseDet.H_nat_le_three
#check @SparseDet.Q_centers
#print axioms SparseDet.Q_centers
#check @SparseDet.F_diagonal
#print axioms SparseDet.F_diagonal
#check @SparseDet.F_factor
#print axioms SparseDet.F_factor
#check @SparseDet.factor_bracket_pos
#print axioms SparseDet.factor_bracket_pos
#check @SparseDet.F_le_diagonal
#print axioms SparseDet.F_le_diagonal
#check @SparseDet.integer_degree_envelope
#print axioms SparseDet.integer_degree_envelope
#check @SparseDet.turningPoint_bounds
#print axioms SparseDet.turningPoint_bounds
#check @SparseDet.phi_two_ninths
#print axioms SparseDet.phi_two_ninths
#check @SparseDet.phi_one
#print axioms SparseDet.phi_one
#check @SparseDet.hasDerivAt_phi
#print axioms SparseDet.hasDerivAt_phi
#check @SparseDet.phi_deriv_factor
#print axioms SparseDet.phi_deriv_factor
#check @SparseDet.phi_left
#print axioms SparseDet.phi_left
#check @SparseDet.phi_middle
#print axioms SparseDet.phi_middle
#check @SparseDet.phi_right
#print axioms SparseDet.phi_right
#check @SparseDet.logarithmic_majorant
#print axioms SparseDet.logarithmic_majorant
#check @SparseDet.trace_square_eigenvalues
#print axioms SparseDet.trace_square_eigenvalues
#check @SparseDet.eigenvalue_le_one_of_quadratic
#print axioms SparseDet.eigenvalue_le_one_of_quadratic
#check @SparseDet.log_det_le_majorant
#print axioms SparseDet.log_det_le_majorant
#check @SparseDet.log_det_le_quadratic
#print axioms SparseDet.log_det_le_quadratic
#check @SparseDet.gram_fourth_moment
#print axioms SparseDet.gram_fourth_moment
#check @SparseDet.sum_square_completion
#print axioms SparseDet.sum_square_completion
#check @SparseDet.normalized_apply
#print axioms SparseDet.normalized_apply
#check @SparseDet.normalized_nonneg
#print axioms SparseDet.normalized_nonneg
#check @SparseDet.normalized_square
#print axioms SparseDet.normalized_square
#check @SparseDet.gram_isHermitian
#print axioms SparseDet.gram_isHermitian
#check @SparseDet.gram_fourth_moment_bound
#print axioms SparseDet.gram_fourth_moment_bound
#check @SparseDet.universal_of_min_degree
#print axioms SparseDet.universal_of_min_degree
#check @SparseDet.absolute_real_of_min_degree
#print axioms SparseDet.absolute_real_of_min_degree
#check @SparseDet.integer_bound_of_min_degree
#print axioms SparseDet.integer_bound_of_min_degree
#check @SparseDet.printed_bound_of_min_degree
#print axioms SparseDet.printed_bound_of_min_degree
#print SparseDet.PrintedConjecture
#print SparseDet.IntegerConjecture
#print SparseDet.MinDegreeEstimate
```

### `SparseAuditFinal.lean`

```lean
import SparseAudit
import SparseFinal

#eval Lean.versionString
#check @SparseDet.edgeCount_eq_sum
#print axioms SparseDet.edgeCount_eq_sum
#check @SparseDet.edgeCount_transpose
#print axioms SparseDet.edgeCount_transpose
#check @SparseDet.rowDegree_transpose
#print axioms SparseDet.rowDegree_transpose
#check @SparseDet.colDegree_transpose
#print axioms SparseDet.colDegree_transpose
#check @SparseDet.identity_zeroOne
#print axioms SparseDet.identity_zeroOne
#check @SparseDet.identity_edgeCount
#print axioms SparseDet.identity_edgeCount
#check @SparseDet.identity_satisfies
#print axioms SparseDet.identity_satisfies
#check @SparseDet.order_zero
#print axioms SparseDet.order_zero
#check @SparseDet.real_bound_of_integer_bound
#print axioms SparseDet.real_bound_of_integer_bound
#check @SparseDet.fano_zeroOne
#print axioms SparseDet.fano_zeroOne
#check @SparseDet.fano_edgeCount
#print axioms SparseDet.fano_edgeCount
#check @SparseDet.fano_det
#print axioms SparseDet.fano_det
#check @SparseDet.fano_attains
#print axioms SparseDet.fano_attains
#check @SparseDet.rowDegree_eq_zero_iff
#print axioms SparseDet.rowDegree_eq_zero_iff
#check @SparseDet.rowDegree_pos_of_det_ne_zero
#print axioms SparseDet.rowDegree_pos_of_det_ne_zero
#check @SparseDet.degree_one_witness
#print axioms SparseDet.degree_one_witness
#check @SparseDet.minor_zeroOne
#print axioms SparseDet.minor_zeroOne
#check @SparseDet.abs_det_delete_row
#print axioms SparseDet.abs_det_delete_row
#check @SparseDet.edgeCount_delete_row
#print axioms SparseDet.edgeCount_delete_row
#check @SparseDet.potential_transpose
#print axioms SparseDet.potential_transpose
#check @SparseDet.potential_leaf_step
#print axioms SparseDet.potential_leaf_step
#check @SparseDet.potential_bound_of_min_degree
#print axioms SparseDet.potential_bound_of_min_degree
#check @SparseDet.log2_bounds
#print axioms SparseDet.log2_bounds
#check @SparseDet.log3_bounds
#print axioms SparseDet.log3_bounds
#check @SparseDet.g_bounds
#print axioms SparseDet.g_bounds
#check @SparseDet.g_neg
#print axioms SparseDet.g_neg
#check @SparseDet.d_pos
#print axioms SparseDet.d_pos
#check @SparseDet.c_add_d_pos
#print axioms SparseDet.c_add_d_pos
#check @SparseDet.L_eq_log
#print axioms SparseDet.L_eq_log
#check @SparseDet.c_add_three_d
#print axioms SparseDet.c_add_three_d
#check @SparseDet.H_three
#print axioms SparseDet.H_three
#check @SparseDet.H_two_lt_three
#print axioms SparseDet.H_two_lt_three
#check @SparseDet.H_four_lt_three
#print axioms SparseDet.H_four_lt_three
#check @SparseDet.J_four_neg
#print axioms SparseDet.J_four_neg
#check @SparseDet.P_pos
#print axioms SparseDet.P_pos
#check @SparseDet.hasDerivAt_H
#print axioms SparseDet.hasDerivAt_H
#check @SparseDet.hasDerivAt_J
#print axioms SparseDet.hasDerivAt_J
#check @SparseDet.J_strictAntiOn
#print axioms SparseDet.J_strictAntiOn
#check @SparseDet.J_neg
#print axioms SparseDet.J_neg
#check @SparseDet.H_strictAntiOn
#print axioms SparseDet.H_strictAntiOn
#check @SparseDet.H_nat_le_three
#print axioms SparseDet.H_nat_le_three
#check @SparseDet.Q_centers
#print axioms SparseDet.Q_centers
#check @SparseDet.F_diagonal
#print axioms SparseDet.F_diagonal
#check @SparseDet.F_factor
#print axioms SparseDet.F_factor
#check @SparseDet.factor_bracket_pos
#print axioms SparseDet.factor_bracket_pos
#check @SparseDet.F_le_diagonal
#print axioms SparseDet.F_le_diagonal
#check @SparseDet.integer_degree_envelope
#print axioms SparseDet.integer_degree_envelope
#check @SparseDet.turningPoint_bounds
#print axioms SparseDet.turningPoint_bounds
#check @SparseDet.phi_two_ninths
#print axioms SparseDet.phi_two_ninths
#check @SparseDet.phi_one
#print axioms SparseDet.phi_one
#check @SparseDet.hasDerivAt_phi
#print axioms SparseDet.hasDerivAt_phi
#check @SparseDet.phi_deriv_factor
#print axioms SparseDet.phi_deriv_factor
#check @SparseDet.phi_left
#print axioms SparseDet.phi_left
#check @SparseDet.phi_middle
#print axioms SparseDet.phi_middle
#check @SparseDet.phi_right
#print axioms SparseDet.phi_right
#check @SparseDet.logarithmic_majorant
#print axioms SparseDet.logarithmic_majorant
#check @SparseDet.trace_square_eigenvalues
#print axioms SparseDet.trace_square_eigenvalues
#check @SparseDet.eigenvalue_le_one_of_quadratic
#print axioms SparseDet.eigenvalue_le_one_of_quadratic
#check @SparseDet.log_det_le_majorant
#print axioms SparseDet.log_det_le_majorant
#check @SparseDet.log_det_le_quadratic
#print axioms SparseDet.log_det_le_quadratic
#check @SparseDet.gram_fourth_moment
#print axioms SparseDet.gram_fourth_moment
#check @SparseDet.sum_square_completion
#print axioms SparseDet.sum_square_completion
#check @SparseDet.normalized_apply
#print axioms SparseDet.normalized_apply
#check @SparseDet.normalized_nonneg
#print axioms SparseDet.normalized_nonneg
#check @SparseDet.normalized_square
#print axioms SparseDet.normalized_square
#check @SparseDet.gram_isHermitian
#print axioms SparseDet.gram_isHermitian
#check @SparseDet.gram_fourth_moment_bound
#print axioms SparseDet.gram_fourth_moment_bound
#check @SparseDet.edgeSum_add
#print axioms SparseDet.edgeSum_add
#check @SparseDet.edgeSum_smul
#print axioms SparseDet.edgeSum_smul
#check @SparseDet.edgeSum_mono
#print axioms SparseDet.edgeSum_mono
#check @SparseDet.row_sum_const
#print axioms SparseDet.row_sum_const
#check @SparseDet.col_sum_const
#print axioms SparseDet.col_sum_const
#check @SparseDet.edgeSum_row
#print axioms SparseDet.edgeSum_row
#check @SparseDet.edgeSum_col
#print axioms SparseDet.edgeSum_col
#check @SparseDet.edgeSum_const
#print axioms SparseDet.edgeSum_const
#check @SparseDet.edgeSum_row_div
#print axioms SparseDet.edgeSum_row_div
#check @SparseDet.edgeSum_col_div
#print axioms SparseDet.edgeSum_col_div
#check @SparseDet.edgeSum_recip
#print axioms SparseDet.edgeSum_recip
#check @SparseDet.degree_edge_envelope
#print axioms SparseDet.degree_edge_envelope
#check @SparseDet.colDegree_pos_of_det_ne_zero
#print axioms SparseDet.colDegree_pos_of_det_ne_zero
#check @SparseDet.realMatrix_det
#print axioms SparseDet.realMatrix_det
#check @SparseDet.normalized_det_ne_zero
#print axioms SparseDet.normalized_det_ne_zero
#check @SparseDet.gram_posDef
#print axioms SparseDet.gram_posDef
#check @SparseDet.log_gram_det
#print axioms SparseDet.log_gram_det
#check @SparseDet.indicator_cauchy
#print axioms SparseDet.indicator_cauchy
#check @SparseDet.transpose_mulVec_normalized
#print axioms SparseDet.transpose_mulVec_normalized
#check @SparseDet.normalized_transpose_contracts
#print axioms SparseDet.normalized_transpose_contracts
#check @SparseDet.gram_contracts
#print axioms SparseDet.gram_contracts
#check @SparseDet.edgeSum_sub
#print axioms SparseDet.edgeSum_sub
#check @SparseDet.trace_gram
#print axioms SparseDet.trace_gram
#check @SparseDet.edgeSum_weight_row
#print axioms SparseDet.edgeSum_weight_row
#check @SparseDet.edgeSum_weight_col
#print axioms SparseDet.edgeSum_weight_col
#check @SparseDet.edgeSum_fourth
#print axioms SparseDet.edgeSum_fourth
#check @SparseDet.edgeSum_centers
#print axioms SparseDet.edgeSum_centers
#check @SparseDet.trace_gram_square_lower
#print axioms SparseDet.trace_gram_square_lower
#check @SparseDet.universal_of_min_degree
#print axioms SparseDet.universal_of_min_degree
#check @SparseDet.absolute_real_of_min_degree
#print axioms SparseDet.absolute_real_of_min_degree
#check @SparseDet.integer_bound_of_min_degree
#print axioms SparseDet.integer_bound_of_min_degree
#check @SparseDet.printed_bound_of_min_degree
#print axioms SparseDet.printed_bound_of_min_degree
#check @SparseDet.edgeSum_F
#print axioms SparseDet.edgeSum_F
#check @SparseDet.min_degree_estimate
#print axioms SparseDet.min_degree_estimate
#check @SparseDet.universal_potential
#print axioms SparseDet.universal_potential
#check @SparseDet.mathdb_348549_integer
#print axioms SparseDet.mathdb_348549_integer
#check @SparseDet.mathdb_348549
#print axioms SparseDet.mathdb_348549

#print SparseDet.mathdb_348549
#print SparseDet.mathdb_348549_integer
```
