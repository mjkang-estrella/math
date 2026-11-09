import Concentration
import Mathlib.Data.Nat.Choose.Sum
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
    · rw [Finset.mul_sum,Finset.mul_sum]
      conv_rhs => rw [← Finset.sum_add_distrib]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro U hU
      have hprod : subsetWeight S (insert a U) q = subsetWeight S U q := by
        apply Finset.prod_congr rfl
        intro i hi
        have : i ≠ a := by intro h; subst i; exact ha hi
        simp [this]
      simp only [subsetWeight,Finset.prod_insert ha,Finset.mem_insert_self,
        ite_true,hn U hU,ite_false] at *
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
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ (sq_pos_of_pos hpos)).mpr
        simpa using hs
      · positivity
    _ = (4/mu^2)*(∑ i ∈ S, q i*(1-q i)) := by
      rw [subsetExpect_scale,subset_card_variance]
    _ ≤ (4/mu^2)*mu := mul_le_mul_of_nonneg_left hv (by positivity)
    _ = 4/(∑ i ∈ S, q i) := by change _ = 4/mu; field_simp

theorem fair_subset_card_law {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ℕ → ℝ) :
    subsetExpect S (fun _ => 1/2) (fun U => f U.card) =
      ∑ j ∈ Finset.range (S.card+1), (fairAtom S.card j : ℝ)*f j := by
  have hw (U : Finset ι) : subsetWeight S U (fun _ => (1:ℝ)/2) = 1/2^S.card := by
    unfold subsetWeight
    simp only [show (1:ℝ)-1/2=1/2 by norm_num,ite_self,Finset.prod_const]
    rw [div_pow,one_pow]
  unfold subsetExpect
  simp only [hw]
  rw [Finset.sum_powerset_apply_card (fun j => (1:ℝ)/2^S.card*f j)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [nsmul_eq_mul,fairAtom,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat]
  ring

theorem fairAtom_good {mu : ℝ} (hmu : 0 < mu) (k j : ℕ)
    (hk : mu/2 ≤ (k:ℝ)) : (fairAtom k j : ℝ) ≤ 2/Real.sqrt mu := by
  have hs := (Rat.cast_le (K := ℝ)).mpr (fairAtom_squared k j)
  push_cast at hs
  have ha : 0 ≤ (fairAtom k j : ℝ) := Rat.cast_nonneg.mpr (fairAtom_nonneg k j)
  have hp := Real.sq_sqrt (le_of_lt hmu)
  have hr := Real.sqrt_pos.mpr hmu
  apply (le_div_iff₀ hr).mpr
  have hm : mu*(fairAtom k j : ℝ)^2 ≤ 4 := by
    nlinarith [sq_nonneg (fairAtom k j : ℝ)]
  nlinarith [sq_nonneg ((fairAtom k j : ℝ)*Real.sqrt mu)]

theorem fair_subset_interval {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ℤ) (h : ℕ) {mu : ℝ} (hmu : 0 < mu)
    (hk : mu/2 ≤ (S.card:ℝ)) :
    subsetExpect S (fun _ => 1/2)
      (fun U => if a ≤ (U.card:ℤ) ∧ (U.card:ℤ) ≤ a+h then 1 else 0) ≤
      2*((h:ℝ)+2)/Real.sqrt mu := by
  rw [fair_subset_card_law S (fun j => if a ≤ (j:ℤ) ∧ (j:ℤ) ≤ a+h then 1 else 0)]
  let J := (Finset.range (S.card+1)).filter (fun j : ℕ => a ≤ (j:ℤ) ∧ (j:ℤ) ≤ a+h)
  have he : (∑ j ∈ Finset.range (S.card+1), (fairAtom S.card j : ℝ)*
      (if a ≤ (j:ℤ) ∧ (j:ℤ) ≤ a+h then 1 else 0)) =
      ∑ j ∈ J, (fairAtom S.card j : ℝ) := by
    simp [J,Finset.sum_filter]
  rw [he]
  have hj : J.card ≤ h+1 := by
    have hinj : Set.InjOn (fun j : ℕ => (j:ℤ)) J := by
      intro x _ y _ he; exact Int.ofNat_inj.mp he
    have hsub : J.image (fun j : ℕ => (j:ℤ)) ⊆ Finset.Icc a (a+h) := by
      intro z hz
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_Icc.mpr (Finset.mem_filter.mp hj).2
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_iff.mpr hinj] at hc
    simp only [Int.card_Icc] at hc
    have he : a+(h:ℤ)+1-a = ((h+1:ℕ):ℤ) := by omega
    rw [he,Int.toNat_natCast] at hc
    exact hc
  calc
    _ ≤ ∑ _j ∈ J, 2/Real.sqrt mu :=
      Finset.sum_le_sum (fun j _ => fairAtom_good hmu S.card j hk)
    _ = (J.card:ℝ)*(2/Real.sqrt mu) := by simp
    _ ≤ ((h:ℝ)+2)*(2/Real.sqrt mu) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have : (J.card:ℝ) ≤ (h:ℝ)+1 := by exact_mod_cast hj
      linarith
    _ = _ := by ring

theorem actual_bad_cell_mass (N M : ℕ) :
    (∑ R ∈ ((completeDomain N).image compress).filter
      (fun R => (markedSlots (initial N) R).card < M), (cellMass N R : ℝ)) =
      (badMarksMass N M : ℝ) := by
  classical
  have he : (∑ R ∈ ((completeDomain N).image compress).filter
      (fun R => (markedSlots (initial N) R).card < M), cellMass N R) =
      badMarksMass N M := by
    unfold badMarksMass
    rw [Finset.sum_filter,Finset.sum_filter]
    calc
      _ = ∑ R ∈ (completeDomain N).image compress,
          ∑ w ∈ cellDomain N R,
            if (markedSlots (initial N) (compress w)).card < M then P N w else 0 := by
        apply Finset.sum_congr rfl
        intro R _
        by_cases hm : (markedSlots (initial N) R).card < M
        · simp only [hm,ite_true,cellMass]
          apply Finset.sum_congr rfl
          intro w hw
          rw [(Finset.mem_filter.mp hw).2]
          simp [hm]
        · simp only [hm,ite_false]
          symm
          apply Finset.sum_eq_zero
          intro w hw
          rw [(Finset.mem_filter.mp hw).2]
          simp [hm]
      _ = _ := Finset.sum_fiberwise_of_maps_to
        (fun w hw => Finset.mem_image_of_mem compress hw) _
  have hc := congrArg (fun q : ℚ => (q:ℝ)) he
  push_cast at hc
  exact hc

theorem subsetWeight_split {ι : Type*} [DecidableEq ι]
    (S U : Finset ι) (q : ι → ℝ) (hU : U ⊆ S) :
    subsetWeight S U q = (∏ i ∈ U, q i)*(∏ i ∈ S \ U, (1-q i)) := by
  unfold subsetWeight
  rw [← Finset.prod_sdiff hU]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi; simp [hi]
  · apply Finset.prod_congr rfl
    intro i hi; simp [(Finset.mem_sdiff.mp hi).2]

theorem thinning_kernel {ι : Type*} [DecidableEq ι]
    (S U T : Finset ι) (p : ι → ℚ) (hU : U ⊆ S) (hT : T ⊆ S) :
    (((∏ i ∈ U, (2*p i) * (if i ∈ T then (1:ℚ)/2 else 1/2)) *
      ∏ i ∈ S \ U, (1-2*p i) * (if i ∈ T then (0:ℚ) else 1) : ℚ) : ℝ) =
    subsetWeight S U (fun i => 2*(p i:ℝ)) *
      (if T ⊆ U then (1:ℝ)/2^U.card else 0) := by
  push_cast
  simp only [ite_self,Finset.prod_mul_distrib,Finset.prod_const]
  rw [subsetWeight_split S U _ hU]
  by_cases ht : T ⊆ U
  · have he : (∏ i ∈ S \ U, if i ∈ T then (0:ℝ) else 1) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      have hn : i ∉ T := fun h => (Finset.mem_sdiff.mp hi).2 (ht h)
      simp [hn]
    simp only [ht,ite_true,he,mul_one,div_pow,one_pow]
    ring
  · obtain ⟨i,hi,hni⟩ := Finset.not_subset.mp ht
    have he : (∏ i ∈ S \ U, if i ∈ T then (0:ℝ) else 1) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨hT hi,hni⟩)
      simp [hi]
    simp [ht,he]

theorem finite_thinning_expectation {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (p : ι → ℚ) (f : Finset ι → ℝ) :
    subsetExpect S (fun i => (p i:ℝ)) f =
    subsetExpect S (fun i => 2*(p i:ℝ))
      (fun U => subsetExpect U (fun _ => 1/2) f) := by
  unfold subsetExpect
  have hv (T : Finset ι) (hT : T ∈ S.powerset) :
      subsetWeight S T (fun i => (p i:ℝ)) =
      ∑ U ∈ S.powerset, subsetWeight S U (fun i => 2*(p i:ℝ))*
        (if T ⊆ U then (1:ℝ)/2^U.card else 0) := by
    have hh := congrArg (fun q : ℚ => (q:ℝ)) (finite_thinning_vector S T p)
    push_cast at hh
    rw [← hh]
    apply Finset.sum_congr rfl
    intro U hU
    exact thinning_kernel S U T p (Finset.mem_powerset.mp hU) (Finset.mem_powerset.mp hT)
  calc
    _ = ∑ T ∈ S.powerset, (∑ U ∈ S.powerset,
        subsetWeight S U (fun i => 2*(p i:ℝ))*
        (if T ⊆ U then (1:ℝ)/2^U.card else 0))*f T := by
      apply Finset.sum_congr rfl
      intro T hT; rw [hv T hT]
    _ = ∑ U ∈ S.powerset, subsetWeight S U (fun i => 2*(p i:ℝ))*
        ∑ T ∈ S.powerset, (if T ⊆ U then (1:ℝ)/2^U.card else 0)*f T := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum,mul_assoc]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro U hU
      congr 1
      have hu := Finset.mem_powerset.mp hU
      have hf : (S.powerset).filter (fun T => T ⊆ U) = U.powerset := by
        ext T
        simp only [Finset.mem_filter,Finset.mem_powerset]
        exact ⟨fun h => h.2,fun h => ⟨h.trans hu,h⟩⟩
      calc
        _ = ∑ T ∈ (S.powerset).filter (fun T => T ⊆ U), (1:ℝ)/2^U.card*f T := by
          simp [Finset.sum_filter,ite_mul]
        _ = ∑ T ∈ U.powerset, subsetWeight U T (fun _ => (1:ℝ)/2)*f T := by
          rw [hf]
          apply Finset.sum_congr rfl
          intro T _
          simp [subsetWeight,show (1:ℝ)-1/2=1/2 by norm_num,div_pow]

end LiteralGame
