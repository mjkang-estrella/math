import ASEPVertex
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option linter.unusedSimpArgs false

/-! From a passing certificate to the hypotheses of `not_extreme_of_dir`. -/

namespace ASEP

open Finset

/-- The real direction encoded by a certificate. -/
noncomputable def vm (c : Cert) : Fin 8 → Fin 8 → ℝ := fun i j => (vZ c.es i j : ℝ)

lemma vZ_nil (i j : Fin 8) : vZ [] i j = 0 := rfl

lemma vZ_cons (e : Fin 8 × Fin 8 × ℤ) (es : List (Fin 8 × Fin 8 × ℤ)) (i j : Fin 8) :
    vZ (e :: es) i j = (if e.1 = i ∧ e.2.1 = j then e.2.2 else 0) + vZ es i j := by
  unfold vZ
  by_cases h : e.1 = i ∧ e.2.1 = j
  · simp [List.filter_cons, h]
  · simp only [List.filter_cons, decide_eq_true_eq, h, ite_false]; simp

/-- Double sums of the encoded direction are filtered list sums. -/
lemma sum_vZ (es : List (Fin 8 × Fin 8 × ℤ)) (A B : Finset (Fin 8)) :
    ∑ i ∈ A, ∑ j ∈ B, vZ es i j = ((es.filter (fun e => decide (e.1 ∈ A ∧ e.2.1 ∈ B))).map (fun e => e.2.2)).sum := by
  induction es with
  | nil => simp [vZ_nil]
  | cons e es ih =>
    simp only [vZ_cons, Finset.sum_add_distrib, ih]
    have h1 : ∑ i ∈ A, ∑ j ∈ B, (if e.1 = i ∧ e.2.1 = j then e.2.2 else 0) =
        if e.1 ∈ A ∧ e.2.1 ∈ B then e.2.2 else 0 := by
      simp_rw [ite_and]
      rw [Finset.sum_comm' (t' := B) (s' := fun _ => A) (by intros; simp [and_comm])]
      simp_rw [Finset.sum_ite_eq]
      by_cases hb : e.2.1 ∈ B <;> by_cases ha : e.1 ∈ A <;> simp [ha, hb]
    rw [h1]
    by_cases h : e.1 ∈ A ∧ e.2.1 ∈ B
    · simp [List.filter_cons, h]
    · simp only [List.filter_cons, decide_eq_true_eq, h, ite_false]; simp

lemma abs_filter_sum_le (es : List (Fin 8 × Fin 8 × ℤ)) (p : Fin 8 × Fin 8 × ℤ → Bool) :
    |((es.filter p).map (fun e => e.2.2)).sum| ≤ (es.map (fun e => |e.2.2|)).sum := by
  induction es with
  | nil => simp
  | cons e es ih =>
    cases hpe : p e
    · simp only [List.filter_cons, hpe, Bool.false_eq_true, ite_false, List.map_cons, List.sum_cons]
      linarith [ih, abs_nonneg e.2.2]
    · simp only [List.filter_cons, hpe, ite_true, List.map_cons, List.sum_cons]
      calc |e.2.2 + ((es.filter p).map (fun e => e.2.2)).sum|
          ≤ |e.2.2| + |((es.filter p).map (fun e => e.2.2)).sum| := abs_add_le _ _
        _ ≤ |e.2.2| + (es.map (fun e => |e.2.2|)).sum := add_le_add le_rfl ih

lemma sum_abs_eq (es : List (Fin 8 × Fin 8 × ℤ)) :
    (es.map (fun e => |e.2.2|)).sum = ((es.map (fun e => e.2.2.natAbs)).sum : ℤ) := by
  induction es with
  | nil => simp
  | cons e es ih => simp [ih, Int.natCast_natAbs]

/-- Unpacking the Boolean checker. -/
lemma chk_spec {c : Cert} (h : chk c = true) :
    (∀ e ∈ c.es, e.1 ≠ e.2.1 ∧ (0 < XN e.1 e.2.1 ∨ c.succ e.1 = e.2.1)) ∧
    (∀ r : Fin 8, ((c.es.filter (fun e => decide (e.1 = r))).map (fun e => e.2.2)).sum = 0) ∧
    (∀ r : Fin 8, ((c.es.filter (fun e => decide (e.2.1 = r))).map (fun e => e.2.2)).sum = 0) ∧
    (∀ S ∈ tightCutList, tourCross c S ≠ 1 ∨ cutSum c.es S = 0) ∧
    (c.es.map (fun e => e.2.2.natAbs)).sum ≤ 64 ∧
    dZ c c.a1 c.a2 * vZ c.es c.b1 c.b2 ≠ dZ c c.b1 c.b2 * vZ c.es c.a1 c.a2 ∧
    (∀ k ∈ List.range 8, c.succ ((0 :: c.tl).getD k 0) = (0 :: c.tl).getD ((k + 1) % 8) 0) := by
  simp only [chk, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.mem_finRange, true_implies] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- A passing certificate defeats the segment from `x*` to the tour of its successor map. -/
theorem not_extreme_of_chk (c : Cert) (h : chk c = true) :
    ¬ IsExtreme ℝ (polytope 8) (segment ℝ xs (fun i j => if c.succ i = j then (1 : ℝ) else 0)) := by
  obtain ⟨k1, k2, k3, k4, k5, k6, _⟩ := chk_spec h
  have hsum : ∀ A B : Finset (Fin 8), ∑ i ∈ A, ∑ j ∈ B, vm c i j =
      ((((c.es.filter (fun e => decide (e.1 ∈ A ∧ e.2.1 ∈ B))).map (fun e => e.2.2)).sum : ℤ) : ℝ) := by
    intro A B; simp only [vm]; rw [← sum_vZ]; push_cast; rfl
  have hzero_entry : ∀ i j, (∀ e ∈ c.es, ¬ (e.1 = i ∧ e.2.1 = j)) → vm c i j = 0 := by
    intro i j hn
    have h0 := hsum {i} {j}
    simp only [Finset.sum_singleton] at h0
    rw [h0, List.filter_eq_nil_iff.2]
    · simp
    intro e he; simp only [Finset.mem_singleton, decide_eq_true_eq]; exact hn e he
  have hbound : ∀ A B : Finset (Fin 8), |∑ i ∈ A, ∑ j ∈ B, vm c i j| ≤ 64 := by
    intro A B; rw [hsum]
    have h1 := abs_filter_sum_le c.es (fun e => decide (e.1 ∈ A ∧ e.2.1 ∈ B))
    have h2 : (c.es.map (fun e => |e.2.2|)).sum ≤ 64 := by
      rw [sum_abs_eq]
      have h64 : (((c.es.map (fun e => e.2.2.natAbs)).sum : ℕ) : ℤ) ≤ ((64 : ℕ) : ℤ) := Int.ofNat_le.mpr k5
      rw [Nat.cast_list_sum, List.map_map] at h64
      exact h64
    have h3 : |((((c.es.filter (fun e => decide (e.1 ∈ A ∧ e.2.1 ∈ B))).map (fun e => e.2.2)).sum : ℤ) : ℝ)| ≤ 64 := by
      rw [← Int.cast_abs]; exact_mod_cast h1.trans h2
    exact h3
  refine not_extreme_of_dir xs (vm c) c.succ xs_mem xs_entry xs_cut ?_ ?_ ?_ ?_ ?_ hbound
    c.a1 c.a2 c.b1 c.b2 ?_
  · intro i; apply hzero_entry; intro e he ⟨h1, h2⟩; exact (k1 e he).1 (h1.trans h2.symm)
  · intro i j hv
    by_contra hcon
    obtain ⟨hc1, hc2⟩ := not_or.1 hcon
    apply hv; apply hzero_entry
    intro e he ⟨h1, h2⟩
    rcases (k1 e he).2 with h3 | h3
    · subst h1; subst h2
      have : (XN e.1 e.2.1 : ℝ) ≠ 0 := by exact_mod_cast h3.ne'
      exact hc1 (div_ne_zero this (by norm_num))
    · exact hc2 (h1 ▸ h2 ▸ h3)
  · intro i
    have h0 := hsum {i} Finset.univ
    simp only [Finset.sum_singleton] at h0
    rw [h0]
    have : (c.es.filter (fun e => decide (e.1 ∈ ({i} : Finset (Fin 8)) ∧ e.2.1 ∈ Finset.univ))) =
        c.es.filter (fun e => decide (e.1 = i)) := by
      apply List.filter_congr; intro e _; simp
    rw [this, k2 i]; simp
  · intro j
    have h0 := hsum Finset.univ {j}
    simp only [Finset.sum_singleton] at h0
    rw [h0]
    have : (c.es.filter (fun e => decide (e.1 ∈ (Finset.univ : Finset (Fin 8)) ∧ e.2.1 ∈ ({j} : Finset (Fin 8))))) =
        c.es.filter (fun e => decide (e.2.1 = j)) := by
      apply List.filter_congr; intro e _; simp
    rw [this, k3 j]; simp
  · intro S h2 h6 hfx hcard
    have hf4 : fluxN S = 4 := by
      rw [flux_xs] at hfx
      have : (fluxN S : ℝ) = 4 := by linarith
      exact_mod_cast this
    obtain ⟨l, hl, rfl⟩ := XN_tight S h2 h6 hf4
    have htc : tourCross c l = 1 := by
      rw [← hcard]; unfold tourCross; congr 1; ext i; simp [List.mem_toFinset]
    rcases k4 l hl with h' | h'
    · exact absurd htc h'
    · unfold flux; rw [hsum]
      have : (c.es.filter (fun e => decide (e.1 ∈ l.toFinset ∧ e.2.1 ∈ (l.toFinset)ᶜ))) =
          c.es.filter (fun e => decide (e.1 ∈ l ∧ e.2.1 ∉ l)) := by
        apply List.filter_congr; intro e _; simp [List.mem_toFinset]
      rw [this]; unfold cutSum at h'; rw [h']; simp
  · intro heq
    apply k6
    have hd : ∀ i j, ((dZ c i j : ℤ) : ℝ) = 4 * (xs i j - (if c.succ i = j then 1 else 0)) := by
      intro i j; simp only [dZ, xs]; push_cast; split_ifs <;> ring
    have : ((dZ c c.a1 c.a2 * vZ c.es c.b1 c.b2 : ℤ) : ℝ) = ((dZ c c.b1 c.b2 * vZ c.es c.a1 c.a2 : ℤ) : ℝ) := by
      push_cast; rw [hd, hd]; simp only [vm] at heq
      calc 4 * (xs c.a1 c.a2 - (if c.succ c.a1 = c.a2 then 1 else 0)) * (vZ c.es c.b1 c.b2 : ℝ)
          = 4 * ((xs c.a1 c.a2 - (if c.succ c.a1 = c.a2 then 1 else 0)) * (vZ c.es c.b1 c.b2 : ℝ)) := by ring
        _ = 4 * ((xs c.b1 c.b2 - (if c.succ c.b1 = c.b2 then 1 else 0)) * (vZ c.es c.a1 c.a2 : ℝ)) := by rw [heq]
        _ = 4 * (xs c.b1 c.b2 - (if c.succ c.b1 = c.b2 then 1 else 0)) * (vZ c.es c.a1 c.a2 : ℝ) := by ring
    exact_mod_cast this

end ASEP
