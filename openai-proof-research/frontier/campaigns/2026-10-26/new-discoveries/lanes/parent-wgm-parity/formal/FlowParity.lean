import Mathlib

open scoped BigOperators

namespace WGMParity

def IntegralReal (x : ℝ) : Prop := ∃ z : ℤ, x = (z : ℝ)

theorem integralReal_two_mul {x : ℝ} (hx : IntegralReal x) :
    IntegralReal (2 * x) := by
  obtain ⟨z, rfl⟩ := hx
  exact ⟨2 * z, by push_cast; ring⟩

theorem integral_flow_of_injective_inputs
    {L I : Type*} [Fintype I] [DecidableEq I]
    (child : I × Bool → L ⊕ I) (hc : Function.Injective child)
    (flow : I → ℝ) (weight : L → ℤ)
    (hleaf : ∀ i b j, child (i, b) = Sum.inl j → flow i = (weight j : ℝ))
    (hnode : ∀ i b j, child (i, b) = Sum.inr j → flow i = 2 * flow j) :
    ∀ i, IntegralReal (flow i) := by
  classical
  let Bad := {i : I // ¬ IntegralReal (flow i)}
  have internal : ∀ p : Bad × Bool, ∃ j : Bad, child (p.1.1, p.2) = Sum.inr j.1 := by
    intro p
    cases h : child (p.1.1, p.2) with
    | inl j =>
        exact False.elim (p.1.2 ⟨weight j, hleaf _ _ _ h⟩)
    | inr j =>
        have hj : ¬ IntegralReal (flow j) := by
          intro hj
          apply p.1.2
          rw [hnode _ _ _ h]
          exact integralReal_two_mul hj
        exact ⟨⟨j, hj⟩, rfl⟩
  let next : Bad × Bool → Bad := fun p => Classical.choose (internal p)
  have next_eq (p : Bad × Bool) :
      child (p.1.1, p.2) = Sum.inr (next p).1 := Classical.choose_spec (internal p)
  have hn : Function.Injective next := by
    intro p q hpq
    have h := hc ((next_eq p).trans (by rw [hpq, ← next_eq q]))
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst h)
    · exact congrArg (fun p : I × Bool => p.2) h
  have hcard := Fintype.card_le_of_injective next hn
  have hzero : Fintype.card Bad = 0 := by
    simp only [Fintype.card_prod, Fintype.card_bool] at hcard
    omega
  intro i
  by_contra hi
  have hpos : 0 < Fintype.card Bad := Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  omega

theorem even_total_of_integral_root (S : ℕ) (t : ℝ)
    (ht : IntegralReal t) (hroot : 2 * t = (S : ℝ)) : Even S := by
  obtain ⟨z, hz⟩ := ht
  have hi : (S : ℤ) = 2 * z := by
    exact_mod_cast (show (S : ℝ) = (2 * z : ℤ) by rw [← hroot, hz]; push_cast; ring)
  have he : Even (S : ℤ) := ⟨z, by omega⟩
  exact_mod_cast he

theorem input_balance_forces_even_total
    {L I : Type*} [Fintype I] [DecidableEq I]
    (child : I × Bool → L ⊕ I) (hc : Function.Injective child)
    (root : I) (flow : I → ℝ) (weight : L → ℤ) (S : ℕ)
    (hleaf : ∀ i b j, child (i, b) = Sum.inl j → flow i = (weight j : ℝ))
    (hnode : ∀ i b j, child (i, b) = Sum.inr j → flow i = 2 * flow j)
    (hroot : 2 * flow root = (S : ℝ)) : Even S := by
  exact even_total_of_integral_root S (flow root)
    (integral_flow_of_injective_inputs child hc flow weight hleaf hnode root) hroot

end WGMParity
