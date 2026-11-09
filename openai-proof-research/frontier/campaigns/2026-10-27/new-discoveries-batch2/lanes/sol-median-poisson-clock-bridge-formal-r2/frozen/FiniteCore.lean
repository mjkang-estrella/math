import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option warningAsError true

namespace MedianTemporal
open scoped BigOperators
abbrev Vertex := Fin 10
abbrev Config := Vertex → Bool

def neighbors (i : Vertex) : List Vertex :=
  match i.val with
  | 0 => [3,5,8]
  | 1 => [2,3,6,9]
  | 2 => [1,3,5,6]
  | 3 => [0,1,2,4,5,8]
  | 4 => [3,6,8]
  | 5 => [0,2,3,7,8,9]
  | 6 => [1,2,4]
  | 7 => [5,9]
  | 8 => [0,3,4,5]
  | _ => [1,5,7]

def vote (s : Config) (i : Vertex) : Bool :=
  let ones := ((neighbors i).filter fun j => s j).length
  let degree := (neighbors i).length
  if degree < 2 * ones then true else if 2 * ones < degree then false else s i

def update (s : Config) (i : Vertex) : Config :=
  fun j => if j = i then vote s i else s j

theorem update_other (s : Config) (i j : Vertex) (h : j ≠ i) :
    update s i j = s j := by simp [update, h]

theorem update_self (s : Config) (i : Vertex) : update s i i = vote s i := by
  simp [update]

noncomputable def bit (s : Config) : ℝ := if s 1 then 1 else 0
noncomputable def T (h : Config → ℝ) (s : Config) : ℝ := ∑ i : Vertex, h (update s i)
noncomputable def Q (h : Config → ℝ) (s : Config) : ℝ := T h s - 10 * h s
noncomputable def drift (s : Config) : ℝ := Q bit s

theorem bit_bounds (s : Config) : 0 ≤ bit s ∧ bit s ≤ 1 := by
  unfold bit; split <;> norm_num

theorem generator (h : Config → ℝ) (s : Config) :
    Q h s = ∑ i : Vertex, (h (update s i) - h s) := by
  simp [Q, T, Finset.sum_sub_distrib]

theorem drift_local (s : Config) : drift s = bit (update s 1) - bit s := by
  rw [drift, generator]
  apply Finset.sum_eq_single (1 : Vertex)
  · intro i _ hi
    simp [bit, update, Ne.symm hi]
  · simp

theorem drift_abs (s : Config) : |drift s| ≤ 1 := by
  rw [drift_local, abs_le]
  have h := bit_bounds s
  have h' := bit_bounds (update s 1)
  constructor <;> linarith

theorem T_bound (h : Config → ℝ) (b : ℝ) (hb : ∀ s, |h s| ≤ b) (s : Config) :
    |T h s| ≤ 10 * b := by
  calc
    |T h s| ≤ ∑ i : Vertex, |h (update s i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Vertex, b := Finset.sum_le_sum fun _ _ => hb _
    _ = 10 * b := by simp

noncomputable def iterate : ℕ → (Config → ℝ) → Config → ℝ
  | 0, h => h
  | k+1, h => T (iterate k h)

theorem iterate_drift_bound (k : ℕ) (s : Config) : |iterate k drift s| ≤ (10 : ℝ)^k := by
  induction k generalizing s with
  | zero => simpa [iterate] using drift_abs s
  | succ k ih =>
    simpa [iterate, pow_succ, mul_comm] using T_bound (iterate k drift) (10^k) ih s

noncomputable def weight (s : Config) : ℝ := ∏ i : Vertex, if s i then 2 else 3
noncomputable def coefficient (k : ℕ) : ℝ := ∑ s : Config, weight s * iterate k drift s

theorem weight_nonneg (s : Config) : 0 ≤ weight s := by
  apply Finset.prod_nonneg
  intro i _
  split <;> norm_num

theorem total_weight : (∑ s : Config, weight s) = (5 : ℝ)^10 := by
  unfold weight
  rw [← Fintype.prod_sum (fun (_i : Vertex) (b : Bool) => (if b then 2 else 3 : ℝ))]
  norm_num [Fintype.sum_bool]

theorem coefficient_bound (k : ℕ) : |coefficient k| ≤ (5 : ℝ)^10 * 10^k := by
  calc
    |coefficient k| ≤ ∑ s : Config, |weight s * iterate k drift s| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s : Config, weight s * (10 : ℝ)^k := by
      apply Finset.sum_le_sum
      intro s _
      rw [abs_mul, abs_of_nonneg (weight_nonneg s)]
      exact mul_le_mul_of_nonneg_left (iterate_drift_bound k s) (weight_nonneg s)
    _ = (5 : ℝ)^10 * 10^k := by rw [← Finset.sum_mul, total_weight]

def wordUpdate : List Vertex → Config → Config
  | [], s => s
  | i :: rest, s => wordUpdate rest (update s i)

theorem wordUpdate_append (a b : List Vertex) (s : Config) :
    wordUpdate (a ++ b) s = wordUpdate b (wordUpdate a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons i rest ih => exact ih (update s i)

def Word : ℕ → Type
  | 0 => Unit
  | k+1 => Vertex × Word k

instance wordFintype : (k : ℕ) → Fintype (Word k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k+1 => @instFintypeProd Vertex (Word k) inferInstance (wordFintype k)

def evalWord : (k : ℕ) → Word k → Config → Config
  | 0, _, s => s
  | k+1, w, s => evalWord k w.2 (update s w.1)

theorem word_count (k : ℕ) : Fintype.card (Word k) = 10^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change Fintype.card (Vertex × Word k) = 10^(k+1)
    rw [Fintype.card_prod, ih]
    simp [pow_succ, mul_comm]

theorem iterate_all_words (k : ℕ) (h : Config → ℝ) (s : Config) :
    iterate k h s = ∑ w : Word k, h (evalWord k w s) := by
  induction k generalizing s with
  | zero =>
    have hc : (Finset.univ : Finset (Word 0)).card = 1 := rfl
    change h s = ∑ _w : Word 0, h s
    rw [Finset.sum_const, hc]
    exact (one_nsmul (h s)).symm
  | succ k ih =>
    change (∑ i : Vertex, iterate k h (update s i)) =
      ∑ w : Vertex × Word k, h (evalWord k w.2 (update s w.1))
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun i _ => ih (update s i))

theorem graph_loopfree : ∀ i : Vertex, i ∉ neighbors i := by decide
theorem graph_symmetric : ∀ i j : Vertex, j ∈ neighbors i ↔ i ∈ neighbors j := by decide
theorem graph_nodup : ∀ i : Vertex, (neighbors i).Nodup := by decide

end MedianTemporal
