import IncidenceBounds
import GeometricBounds

open scoped BigOperators

namespace MaxIndex

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
theorem probability_le_one (p : α → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (u : α) : p u ≤ 1 := by
  rw [← hsum]
  exact Finset.single_le_sum (fun i _ => hp i) (Finset.mem_univ u)

theorem probability_tail_le (p : α → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (u i : α) (hi : i ≠ u) : p i ≤ 1 - p u := by
  have htail : (∑ j ∈ Finset.univ.erase u, p j) + p u = 1 := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ u), hsum]
  have hle : p i ≤ ∑ j ∈ Finset.univ.erase u, p j := by
    exact Finset.single_le_sum (fun j _ => hp j) (by simp [hi])
  linarith

omit [Fintype α] [DecidableEq α] in
theorem geometricEntry_nonneg (p : α → ℝ) (e : α × α) :
    0 ≤ geometricEntry p e := Real.sqrt_nonneg _

omit [Fintype α] [DecidableEq α] in
theorem geometricEntry_sq (p : α → ℝ) (hp : ∀ i, 0 ≤ p i) (e : α × α) :
    (geometricEntry p e) ^ 2 = p e.1 * p e.2 :=
  Real.sq_sqrt (mul_nonneg (hp _) (hp _))

omit [DecidableEq α] in
theorem geometricEntry_unit (p : α → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) : ∑ e, (geometricEntry p e) ^ 2 = 1 := by
  simp_rw [geometricEntry_sq p hp]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, hsum, mul_one]
  exact hsum

omit [Fintype α] [DecidableEq α] in
theorem geometricEntry_diagonal (p : α → ℝ) (hp : ∀ i, 0 ≤ p i) (u : α) :
    geometricEntry p (u, u) = p u := by
  simpa only [geometricEntry, ← pow_two] using Real.sqrt_sq (hp u)

omit [Fintype α] [DecidableEq α] in
theorem geometricEntry_le_maximum (p : α → ℝ) (hp : ∀ i, 0 ≤ p i)
    (u : α) (hu : ∀ i, p i ≤ p u) (e : α × α) :
    geometricEntry p e ≤ p u := by
  have hprod : p e.1 * p e.2 ≤ p u * p u :=
    mul_le_mul (hu _) (hu _) (hp _) (hp _)
  have hsq := geometricEntry_sq p hp e
  have hn := geometricEntry_nonneg p e
  nlinarith [hp u]

theorem geometric_low_bound (p : α → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (k : ℕ) :
    maskTopSum (geometricEntry p) k ≤ Real.sqrt k :=
  maskTopSum_le_sqrt _ _ (geometricEntry_unit p hp hsum)

theorem geometric_high_bound (p : α → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (u : α) (hu : ∀ i, p i ≤ p u)
    (m : ℕ) (hk : 2 * m + 1 ≤ Fintype.card (α × α)) :
    maskTopSum (geometricEntry p) (2 * m + 1) ≤
      p u + Real.sqrt (2 * (m : ℝ)) * Real.sqrt (1 - (p u) ^ 2) := by
  have h := maskTopSum_le_head_sqrt (geometricEntry p) (geometricEntry_nonneg p)
    (geometricEntry_unit p hp hsum) (2 * m + 1) (by omega) hk (u, u)
    (fun e => by rw [geometricEntry_diagonal p hp u]; exact geometricEntry_le_maximum p hp u hu e)
  rw [geometricEntry_diagonal p hp u] at h
  norm_num only [Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_ofNat] at h
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * (m : ℝ))] at h
  exact h

end MaxIndex
