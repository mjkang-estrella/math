import UpperFamilies
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace WheelFormal
attribute [local instance] Classical.propDecidable

/-- The even representatives strictly below the last representative. -/
theorem alternating_card (t : ℕ) :
    (Finset.univ.filter (alternating t)).card = t := by
  classical
  let f : Fin t → ZMod (2*t+1) := fun k => (2*k.val : ℕ)
  have hv : ∀ k, (f k).val = 2*k.val := by
    intro k
    exact (ZMod.val_natCast _ _).trans (Nat.mod_eq_of_lt (by have := k.isLt; omega))
  have hinj : Function.Injective f := by
    intro a b he
    have hh := congrArg ZMod.val he
    rw [hv,hv] at hh
    apply Fin.ext
    omega
  have he : Finset.univ.filter (alternating t) = Finset.univ.image f := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hx
      refine ⟨⟨x.val/2, by unfold alternating at hx; omega⟩, ?_⟩
      apply ZMod.val_injective
      rw [hv]
      unfold alternating at hx
      dsimp
      omega
    · rintro ⟨k,rfl⟩
      unfold alternating
      rw [hv]
      have := k.isLt
      omega
  rw [he,Finset.card_image_of_injective _ hinj]
  simp

theorem sum_sub_reindex (t : ℕ) (x : ZMod (2*t+1)) (f : ZMod (2*t+1) → ℝ) :
    (∑ a, f (x-a)) = ∑ a, f a := by
  classical
  exact Fintype.sum_equiv
    (⟨fun a => x-a, fun a => x-a, by intro a; dsimp; ring, by intro a; dsimp; ring⟩)
    _ _ (by intro a; rfl)

theorem alternating_fibre (t : ℕ) (x : ZMod (2*t+1)) :
    (∑ a, if alternating t (x-a) then (1:ℝ) else 0) = t := by
  classical
  rw [sum_sub_reindex t x (fun z => if alternating t z then (1:ℝ) else 0)]
  have hc := alternating_card t
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast hc

theorem last_fibre (t : ℕ) (x : ZMod (2*t+1)) :
    (∑ a, if (x-a).val = 2*t then (1:ℝ) else 0) = 1 := by
  classical
  rw [sum_sub_reindex t x (fun z => if z.val = 2*t then (1:ℝ) else 0)]
  have hh : ∀ a : ZMod (2*t+1), a.val = 2*t ↔ a = (2*t : ℕ) := by
    intro a
    constructor
    · intro he; rw [← ZMod.natCast_zmod_val a, he]
    · intro he; rw [he, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  simp_rw [hh]
  simp

def ordinaryRole (t : ℕ) (x : ZMod (2*t+1)) : Prop :=
  ¬ alternating t x ∧ x.val ≠ 2*t

theorem ordinary_fibre (t : ℕ) (x : ZMod (2*t+1)) :
    (∑ a, if ordinaryRole t (x-a) then (1:ℝ) else 0) = t := by
  classical
  have hp : ∀ a : ZMod (2*t+1),
      (if alternating t (x-a) then (1:ℝ) else 0) +
      (if ordinaryRole t (x-a) then 1 else 0) +
      (if (x-a).val = 2*t then 1 else 0) = 1 := by
    intro a
    unfold ordinaryRole alternating
    split_ifs <;> norm_num at * <;> omega
  have hs := congrArg (fun f : ZMod (2*t+1) → ℝ => ∑ a, f a) (funext hp)
  simp only [Finset.sum_add_distrib, alternating_fibre, last_fibre,
    Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one] at hs
  push_cast at hs
  linarith

theorem family0_rim_count (t : ℕ) (i j : ZMod (2*t+1)) :
    (∑ s, if (some i,some j) ∈ family0 t s then (1:ℝ) else 0) = t := by
  classical
  simpa only [family0,profileFamily,Finset.mem_filter,Finset.mem_univ,true_and]
    using alternating_fibre t (i-j)

theorem family2_rim_count (t : ℕ) (i j : ZMod (2*t+1)) :
    (∑ a, ∑ b, if (some i,some j) ∈ family2 t a b then (1:ℝ) else 0) =
      (t:ℝ)^2+1 := by
  classical
  have he : ∀ a b : ZMod (2*t+1),
      (if (some i,some j) ∈ family2 t a b then (1:ℝ) else 0) =
      (if ordinaryRole t (i-a) then 1 else 0)*(if ordinaryRole t (j-b) then 1 else 0) +
      (if (i-a).val = 2*t then 1 else 0)*(if (j-b).val = 2*t then 1 else 0) := by
    intro a b
    have hm : (some i,some j) ∈ family2 t a b ↔ roleRim t a b i j := by
      simp [family2,profileFamily]
    simp only [hm]
    unfold roleRim
    unfold ordinaryRole
    by_cases ha : alternating t (i-a) <;>
      by_cases hb : alternating t (j-b) <;>
      by_cases hla : (i-a).val = 2*t <;>
      by_cases hlb : (j-b).val = 2*t <;>
      simp [Finset.mem_filter,ha,hb,hla,hlb] <;> unfold alternating at * <;> omega
  simp_rw [he,Finset.sum_add_distrib,← Finset.mul_sum]
  simp_rw [ordinary_fibre,last_fibre]
  simp only [mul_one,← Finset.sum_mul]
  rw [ordinary_fibre,last_fibre]
  ring
end WheelFormal
