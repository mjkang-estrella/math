import TreeSwitch
import OrderedTreeCheck
namespace Nut8

/-- Extend a finite ordered parent function to the naturals for treeSign. -/
def parentExtension (p : Fin 8 → Fin 8) (n : Nat) : Nat :=
  if h : n < 8 then (p ⟨n,h⟩).val else 0

lemma parentExtension_lt (p : Fin 8 → Fin 8)
    (hp : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val) :
    ∀ n, 0 < n → parentExtension p n < n := by
  intro n hn
  unfold parentExtension
  split_ifs with hb
  · exact hp ⟨n,hb⟩ (by intro he; have := congrArg Fin.val he; simp only [Fin.val_zero] at this; omega)
  · exact hn

/-- Any ordered parent data normalize simultaneously, including nonunit weights. -/
theorem ordered_switch_exists (C : QuotientMatrix) (p : Fin 8 → Fin 8)
    (hp : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val) :
    ∃ d : Fin 8 → ℤ, (∀ i, d i = 1 ∨ d i = -1) ∧
      ∀ i : Fin 8, i ≠ 0 → switch d C (p i) i = |C (p i) i| := by
  let v : Nat → ℤ := fun n => if h : n < 8 then C (p ⟨n,h⟩) ⟨n,h⟩ else 0
  let w : Nat → ℤ := fun n => if v n < 0 then -1 else 1
  have hw : ∀ n, w n = 1 ∨ w n = -1 := by
    intro n
    dsimp [w]
    split_ifs <;> simp
  have hv : ∀ n, v n = w n * |v n| := by
    intro n
    dsimp [w]
    split_ifs with hn
    · rw [abs_of_neg hn]; ring
    · rw [abs_of_nonneg (le_of_not_gt hn), one_mul]
  let d : Fin 8 → ℤ := fun i => treeSign (parentExtension p) (parentExtension_lt p hp) w i.val
  refine ⟨d, fun i => treeSign_unit _ _ w hw i.val, ?_⟩
  intro i hn
  have hn' : i.val ≠ 0 := fun he => hn (Fin.ext he)
  have ht := treeSign_weight (parentExtension p) (parentExtension_lt p hp) w hw v hv i.val hn'
  simpa only [parentExtension, i.isLt, ↓reduceDIte, v, d, switch] using ht
end Nut8
