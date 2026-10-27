import CircuitCount

open scoped BigOperators

namespace WGMParity

noncomputable def inputFlow {L I : Type*} [Fintype I]
    (child : I × Bool → L ⊕ I) (flow : I → ℝ) (v : L ⊕ I) : ℝ := by
  classical
  exact ∑ p : I × Bool, if child p = v then flow p.1 else 0

theorem inputFlow_of_hit {L I : Type*} [Fintype I]
    (child : I × Bool → L ⊕ I) (hc : Function.Injective child)
    (flow : I → ℝ) (p : I × Bool) : inputFlow child flow (child p) = flow p.1 := by
  classical
  unfold inputFlow
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _ hqp
    simp only [hc.eq_iff]
    exact ite_eq_right hqp
  · simp

theorem inputFlow_of_miss {L I : Type*} [Fintype I]
    (child : I × Bool → L ⊕ I) (flow : I → ℝ) (v : L ⊕ I)
    (hv : ∀ p, child p ≠ v) : inputFlow child flow v = 0 := by
  classical
  simp [inputFlow, hv]

noncomputable def flowMatrix {L I : Type*} [Fintype I]
    (child : I × Bool → L ⊕ I) : Matrix I I ℝ := by
  classical
  exact fun j i => (if j = i then 2 else 0) -
    ∑ b : Bool, if child (i, b) = Sum.inr j then 1 else 0

theorem flowMatrix_mulVec {L I : Type*} [Fintype I]
    (child : I × Bool → L ⊕ I) (f : I → ℝ) (j : I) :
    (flowMatrix child).mulVec f j = 2 * f j - inputFlow child f (Sum.inr j) := by
  classical
  simp only [flowMatrix, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · simp [ite_mul]
  · simp only [inputFlow, Fintype.sum_prod_type, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> simp

theorem flowMatrix_mulVec_injective {L I : Type*} [Fintype I]
    (child : I × Bool → L ⊕ I) (hc : Function.Injective child) :
    Function.Injective (flowMatrix child).mulVec := by
  classical
  suffices hker : ∀ f : I → ℝ, (flowMatrix child).mulVec f = 0 → f = 0 by
    intro x y hxy
    have hh : (flowMatrix child).mulVec (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hker (x - y) hh)
  intro f hf
  by_cases hI : Nonempty I
  · let := hI
    obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun i => |f i|)
      Finset.univ_nonempty
    have hz : |f j| = 0 := by
      have he : 2 * f j = inputFlow child f (Sum.inr j) := by
        have := congrFun hf j
        rw [flowMatrix_mulVec] at this
        simpa using (sub_eq_zero.mp this)
      by_cases hh : ∃ p, child p = Sum.inr j
      · obtain ⟨p, hp⟩ := hh
        rw [← hp, inputFlow_of_hit child hc f p] at he
        have hmax := hj p.1 (Finset.mem_univ _)
        have habs := congrArg abs he
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at habs
        have hnon := abs_nonneg (f j)
        linarith
      · rw [inputFlow_of_miss child f _ (by simpa using hh)] at he
        have : f j = 0 := by linarith
        simp [this]
    funext i
    have hi := hj i (Finset.mem_univ _)
    have : |f i| = 0 := le_antisymm (by simpa [hz] using hi) (abs_nonneg _)
    exact abs_eq_zero.mp this
  · have : IsEmpty I := not_nonempty_iff.mp hI
    exact Subsingleton.elim _ _

theorem exists_balance_flow {L I : Type*} [Fintype I] [DecidableEq I]
    (child : I × Bool → L ⊕ I) (hc : Function.Injective child)
    (root : I) (S : ℝ) : ∃ flow : I → ℝ,
    ∀ j, 2 * flow j - inputFlow child flow (Sum.inr j) = if j = root then S else 0 := by
  classical
  have hu : IsUnit (flowMatrix child) :=
    Matrix.mulVec_injective_iff_isUnit.mp (flowMatrix_mulVec_injective child hc)
  have hs := Matrix.mulVec_surjective_iff_isUnit.mpr hu
  obtain ⟨flow, hf⟩ := hs (fun j => if j = root then S else 0)
  refine ⟨flow, fun j => ?_⟩
  simpa only [flowMatrix_mulVec] using congrFun hf j

end WGMParity
