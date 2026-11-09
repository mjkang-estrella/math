import CountR7CExpansion
noncomputable section
open scoped BigOperators
namespace ChanLevine.Round7C
open Round6 Round3
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- With no chips, avoiding facing pairs forces a constant rotor. -/
theorem no_facing_iff_constant (q : ZMod n → Bool) :
    (∀ v, ¬ (q v = true ∧ q (v+1) = false)) ↔
      (q = fun _ => true) ∨ (q = fun _ => false) := by
  constructor
  · intro h
    by_cases ht : ∃ v, q v = true
    · obtain ⟨v,hv⟩ := ht
      left
      have step (u : ZMod n) (hu : q u = true) : q (u+1) = true := by
        cases he : q (u+1)
        · exact False.elim (h u ⟨hu,he⟩)
        · rfl
      have spread (a : ℕ) : q (v+(a : ZMod n)) = true := by
        induction a with
        | zero => simpa using hv
        | succ a ih => simpa [Nat.cast_add, add_assoc] using step _ ih
      funext u
      have hu := spread (u-v).val
      simpa using hu
    · right
      funext u
      cases he : q u
      · rfl
      · exact False.elim (ht ⟨u,he⟩)
  · rintro (rfl | rfl) <;> simp

/-- Exact zero-level chip sum: the unique chip function is identically zero. -/
theorem chipSum_zero {F : Type*} [CommRing F] (z : F) (s : Finset (ZMod n)) :
    chipSum z s 0 = 1 := by
  let x0 : BoundedChips n 0 := ⟨fun _ => 0, by simp⟩
  have hu : (Finset.univ : Finset (BoundedChips n 0)) = {x0} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    apply Subtype.ext
    funext v
    apply Fin.ext
    have h := (x.val v).isLt
    simp only [x0, Fin.val_zero]
    omega
  simp [chipSum, hu, x0]

/-- Only the two empty constant rotors survive the local cycle test. -/
theorem empty_rotor_sum {F : Type*} [CommRing F] (z : F) :
    (∑ q : ZMod n → Bool, (∏ v, if q v then 1 else z) *
      (if ∀ v, ¬ (q v = true ∧ q (v+1) = false) then 1 else 0)) = 1+z^n := by
  let e : Bool → (ZMod n → Bool) := fun b _ => b
  have he : Function.Injective e := by
    intro a b h
    exact congrFun h 0
  have hs := Fintype.sum_of_injective e he
    (fun b => if b then (1 : F) else z^n)
    (fun q => (∏ v, if q v then (1 : F) else z) *
      (if ∀ v, ¬ (q v = true ∧ q (v+1) = false) then 1 else 0))
    (by
      intro q hq
      have h : ¬ ∀ v, ¬ (q v = true ∧ q (v+1) = false) := by
        intro h
        rcases (no_facing_iff_constant q).mp h with h | h
        · exact hq ⟨true,h.symm⟩
        · exact hq ⟨false,h.symm⟩
      simp only [ite_eq_right h, mul_zero])
    (by intro b; cases b <;> simp [e])
  rw [← hs]
  simp [add_comm]

/-- The completed zero coefficient follows from the same matching expansion. -/
theorem matchingSeries_zero {F : Type*} [CommRing F] (z : F) :
    matchingSeries (n := n) z 0 = 1+z^n := by
  have hprod (q : ZMod n → Bool) :
      (if ∀ v, ¬ (q v = true ∧ q (v+1) = false) then (1 : F) else 0) =
        ∏ v, (1 - if q v = true ∧ q (v+1) = false then 1 else 0) := by
    by_cases h : ∀ v, ¬ (q v = true ∧ q (v+1) = false)
    · simp [h]
    · rw [ite_eq_right h]
      push Not at h
      obtain ⟨v,hv⟩ := h
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv])
  have hie (q : ZMod n → Bool) :
      (∏ v, if q v then (1 : F) else z) *
        (if ∀ v, ¬ (q v = true ∧ q (v+1) = false) then 1 else 0) =
      ∑ s ∈ (Finset.univ : Finset (ZMod n)).powerset,
        (-1 : F)^s.card * (∏ v, if q v then 1 else z) *
          (if ∀ v ∈ s, q v = true ∧ q (v+1) = false then 1 else 0) := by
    rw [hprod, Finset.prod_sub, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    have hp : (∏ v ∈ s, if q v = true ∧ q (v+1) = false then (1 : F) else 0) =
        if ∀ v ∈ s, q v = true ∧ q (v+1) = false then 1 else 0 := by
      split_ifs with h
      · exact Finset.prod_eq_one (fun v hv => ite_eq_left (h v hv))
      · push Not at h
        obtain ⟨v,hv,he⟩ := h
        exact Finset.prod_eq_zero hv (ite_eq_right (fun hh => he hh.1 hh.2))
    rw [hp]
    simp only [Finset.prod_const_one]
    ring
  rw [← empty_rotor_sum z]
  simp_rw [hie]
  rw [Finset.sum_comm]
  unfold matchingSeries
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : Matching s
  · rw [ite_eq_left hs, chipSum_zero, mul_one]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [forced_rotor_sum z s hs, neg_eq_neg_one_mul, mul_pow]
    ring
  · rw [ite_eq_right hs]
    symm
    apply Finset.sum_eq_zero
    intro q _
    have hn : ¬ ∀ v ∈ s, q v = true ∧ q (v+1) = false := by
      intro h
      apply hs
      apply facing_matching (Config.mk (fun _ => 0) q) s
      intro v hv
      exact ⟨(h v hv).1, (h v hv).2, rfl, rfl⟩
    simp [hn]

theorem frequencyRoot_pow_n (k : ZMod n) : frequencyRoot n k ^ n = 1 := by
  rw [frequencyRoot, ← AddChar.map_nsmul_eq_pow]
  simp [nsmul_eq_mul]

theorem completed_matching (m : ℕ) (k : ZMod n) :
    completedFourier n k m = matchingSeries (n := n) (frequencyRoot n k) m := by
  by_cases hm : m = 0
  · subst m
    simp only [completedFourier, ite_true, matchingSeries_zero, frequencyRoot_pow_n]
    ring
  · simp only [completedFourier, hm, ite_false]
    exact fourier_matching m (Nat.pos_of_ne_zero hm) k
end ChanLevine.Round7C
