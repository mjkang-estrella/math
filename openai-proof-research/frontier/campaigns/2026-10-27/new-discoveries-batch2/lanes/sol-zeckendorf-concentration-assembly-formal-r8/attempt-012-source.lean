import Concentration
set_option autoImplicit false
namespace LiteralGame
attribute [local instance] Classical.propDecidable

noncomputable def subsetWeight {ι : Type*} [DecidableEq ι]
    (S U : Finset ι) (q : ι → ℝ) : ℝ :=
  ∏ i ∈ S, if i ∈ U then q i else 1-q i

noncomputable def subsetExpect {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (q : ι → ℝ) (f : Finset ι → ℝ) : ℝ :=
  ∑ U ∈ S.powerset, subsetWeight S U q * f U

theorem subsetExpect_insert {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι) (ha : a ∉ S) (q : ι → ℝ) (f : Finset ι → ℝ) :
    subsetExpect (insert a S) q f =
      (1-q a)*subsetExpect S q f +
      q a*subsetExpect S q (fun U => f (insert a U)) := by
  classical
  have hn (U : Finset ι) (hU : U ∈ S.powerset) : a ∉ U :=
    fun h => ha (Finset.mem_powerset.mp hU h)
  unfold subsetExpect
  rw [Finset.powerset_insert,Finset.sum_union]
  · rw [Finset.sum_image]
    · rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro U hU
      have hprod : subsetWeight S (insert a U) q = subsetWeight S U q := by
        apply Finset.prod_congr rfl
        intro i hi
        have : i ≠ a := by intro h; subst i; exact ha hi
        simp [this]
      simp only [subsetWeight,Finset.prod_insert ha,Finset.mem_insert_self,
        if_true,hn U hU,if_false] at *
      rw [hprod]
      ring
    · intro U hU V hV h
      have he := congrArg (Finset.erase · a) h
      simpa [Finset.erase_insert (hn U hU),Finset.erase_insert (hn V hV)] using he
  · apply Finset.disjoint_left.mpr
    intro U hU hV
    obtain ⟨V,hV,rfl⟩ := Finset.mem_image.mp hV
    exact hn _ hU (Finset.mem_insert_self _ _)

theorem subsetExpect_const {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (q : ι → ℝ) (c : ℝ) : subsetExpect S q (fun _ => c) = c := by
  induction S using Finset.induction_on with
  | empty => simp [subsetExpect,subsetWeight]
  | @insert a S ha ih => rw [subsetExpect_insert S a ha,ih]; ring

theorem subsetExpect_add {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (q : ι → ℝ) (f g : Finset ι → ℝ) :
    subsetExpect S q (fun U => f U + g U) = subsetExpect S q f + subsetExpect S q g := by
  simp [subsetExpect,mul_add,Finset.sum_add_distrib]

theorem subsetExpect_scale {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (q : ι → ℝ) (c : ℝ) (f : Finset ι → ℝ) :
    subsetExpect S q (fun U => c*f U) = c*subsetExpect S q f := by
  simp [subsetExpect,Finset.mul_sum,mul_left_comm]

theorem subsetExpect_congr {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (q : ι → ℝ) (f g : Finset ι → ℝ)
    (h : ∀ U ∈ S.powerset, f U = g U) : subsetExpect S q f = subsetExpect S q g := by
  exact Finset.sum_congr rfl (fun U hU => congrArg (subsetWeight S U q * ·) (h U hU))

theorem subset_card_mean {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (q : ι → ℝ) :
    subsetExpect S q (fun U => (U.card : ℝ)) = ∑ i ∈ S, q i := by
  induction S using Finset.induction_on with
  | empty => simp [subsetExpect,subsetWeight]
  | @insert a S ha ih =>
    rw [subsetExpect_insert S a ha]
    have he : subsetExpect S q (fun U => ((insert a U).card : ℝ)) =
        subsetExpect S q (fun U => (U.card : ℝ)+1) := by
      apply subsetExpect_congr
      intro U hU
      have hn : a ∉ U := fun h => ha (Finset.mem_powerset.mp hU h)
      simp [Finset.card_insert_of_notMem hn]
    rw [he,subsetExpect_add,subsetExpect_const,ih,Finset.sum_insert ha]
    ring

theorem subset_card_second {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (q : ι → ℝ) :
    subsetExpect S q (fun U => (U.card : ℝ)^2) =
      (∑ i ∈ S, q i)^2 + ∑ i ∈ S, q i*(1-q i) := by
  induction S using Finset.induction_on with
  | empty => simp [subsetExpect,subsetWeight]
  | @insert a S ha ih =>
    rw [subsetExpect_insert S a ha]
    have he : subsetExpect S q (fun U => ((insert a U).card : ℝ)^2) =
        subsetExpect S q (fun U => (U.card : ℝ)^2 + (2*(U.card : ℝ)+1)) := by
      apply subsetExpect_congr
      intro U hU
      have hn : a ∉ U := fun h => ha (Finset.mem_powerset.mp hU h)
      simp only [Finset.card_insert_of_notMem hn,Nat.cast_add,Nat.cast_one]
      ring
    rw [he,subsetExpect_add,subsetExpect_add,subsetExpect_const,
      subsetExpect_scale,subset_card_mean,ih,Finset.sum_insert ha,Finset.sum_insert ha]
    ring

theorem subset_card_variance {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (q : ι → ℝ) :
    subsetExpect S q (fun U => ((U.card : ℝ) - ∑ i ∈ S, q i)^2) =
      ∑ i ∈ S, q i*(1-q i) := by
  have he : subsetExpect S q (fun U => ((U.card : ℝ) - ∑ i ∈ S, q i)^2) =
      subsetExpect S q (fun U => (U.card : ℝ)^2 +
        ((-2*(∑ i ∈ S, q i))*(U.card : ℝ)+(∑ i ∈ S, q i)^2)) := by
    apply subsetExpect_congr; intro U _; ring
  rw [he,subsetExpect_add,subsetExpect_add,subsetExpect_scale,
    subsetExpect_const,subset_card_mean,subset_card_second]
  ring

theorem subsetWeight_nonneg {ι : Type*} [DecidableEq ι]
    (S U : Finset ι) (q : ι → ℝ) (hq : ∀ i ∈ S, 0 ≤ q i ∧ q i ≤ 1) :
    0 ≤ subsetWeight S U q := by
  apply Finset.prod_nonneg
  intro i hi
  split_ifs <;> linarith [(hq i hi).1,(hq i hi).2]

theorem subsetExpect_mono {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (q : ι → ℝ) (hq : ∀ i ∈ S, 0 ≤ q i ∧ q i ≤ 1)
    (f g : Finset ι → ℝ) (h : ∀ U ∈ S.powerset, f U ≤ g U) :
    subsetExpect S q f ≤ subsetExpect S q g := by
  exact Finset.sum_le_sum (fun U hU =>
    mul_le_mul_of_nonneg_left (h U hU) (subsetWeight_nonneg S U q hq))

theorem finite_card_chebyshev {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (q : ι → ℝ) (hq : ∀ i ∈ S, 0 ≤ q i ∧ q i ≤ 1)
    (hmu : 0 < ∑ i ∈ S, q i) :
    subsetExpect S q (fun U => if (U.card : ℝ) < (∑ i ∈ S, q i)/2 then 1 else 0) ≤
      4/(∑ i ∈ S, q i) := by
  let mu := ∑ i ∈ S, q i
  have hpos : 0 < mu := hmu
  have hv : (∑ i ∈ S, q i*(1-q i)) ≤ mu := by
    apply Finset.sum_le_sum
    intro i hi
    nlinarith [sq_nonneg (q i)]
  calc
    _ ≤ subsetExpect S q (fun U => (4/mu^2)*((U.card : ℝ)-mu)^2) := by
      apply subsetExpect_mono S q hq
      intro U _
      split_ifs with h
      · have hs : mu^2 ≤ 4*((U.card : ℝ)-mu)^2 := by
          have hn : (0:ℝ) ≤ U.card := Nat.cast_nonneg _
          dsimp [mu] at *
          nlinarith
        apply (le_div_iff₀ (sq_pos_of_pos hpos)).mpr
        simpa [div_mul_eq_mul_div] using hs
      · positivity
    _ = (4/mu^2)*(∑ i ∈ S, q i*(1-q i)) := by
      rw [subsetExpect_scale,subset_card_variance]
    _ ≤ (4/mu^2)*mu := mul_le_mul_of_nonneg_left hv (by positivity)
    _ = 4/(∑ i ∈ S, q i) := by change _ = 4/mu; field_simp; ring

end LiteralGame
