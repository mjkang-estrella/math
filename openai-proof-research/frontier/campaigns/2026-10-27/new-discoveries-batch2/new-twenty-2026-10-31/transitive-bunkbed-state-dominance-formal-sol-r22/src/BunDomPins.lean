import BunDomFiber
namespace BunDom
open Classical
variable {α : Type} [Fintype α]

noncomputable def pinEquiv (P : α → Prop) :
    {f : α → Bool // ∀ a, P a → f a = false} ≃ ({a : α // ¬ P a} → Bool) where
  toFun f a := f.1 a.1
  invFun g := ⟨fun a => if h : P a then false else g ⟨a,h⟩,
    by intro a ha; simp [ha]⟩
  left_inv f := by
    apply Subtype.ext
    funext a
    by_cases h : P a
    · simp [h, f.2 a h]
    · simp [h]
  right_inv g := by
    funext a
    simp [a.2]

theorem pin_card (P : α → Prop) :
    Fintype.card {f : α → Bool // ∀ a, P a → f a = false} =
      2 ^ (Fintype.card α - Fintype.card {a // P a}) := by
  rw [Fintype.card_congr (pinEquiv P), Fintype.card_fun,
    Fintype.card_bool, Fintype.card_subtype_compl]

theorem hit_card (P : α → Prop) :
    Fintype.card {f : α → Bool // ∃ a, P a ∧ f a = true} =
      2 ^ Fintype.card α - 2 ^ (Fintype.card α - Fintype.card {a // P a}) := by
  let Q := fun f : α → Bool => ∀ a, P a → f a = false
  have he : {f : α → Bool // ∃ a, P a ∧ f a = true} ≃ {f : α → Bool // ¬ Q f} :=
    Equiv.subtypeEquivRight (fun f => by
      simp only [Q, not_forall]
      constructor
      · rintro ⟨a,ha,hf⟩
        exact ⟨a,ha,by simp [hf]⟩
      · rintro ⟨a,ha,hf⟩
        exact ⟨a,ha,by cases h : f a <;> simp_all⟩)
  rw [Fintype.card_congr he, Fintype.card_subtype_compl,
    Fintype.card_fun, Fintype.card_bool]
  rw [pin_card P]
end BunDom
