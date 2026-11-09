import BunDomPins
namespace BunDom
open Classical

noncomputable def zeroFreshEquiv (j : Nat) (P : Fin (j+1) × Bool → Prop) :
    {f : Fresh j // ∀ i l, P (i,l) → f.1 i l = false} ≃
      (({x : Fin (j+1) × Bool // ¬ P x} → Bool) × Bool) where
  toFun f := (fun x => f.1.1 x.1.1 x.1.2, f.1.2)
  invFun g := ⟨(fun i l => if h : P (i,l) then false else g.1 ⟨(i,l),h⟩, g.2),
    by intro i l h; simp [h]⟩
  left_inv f := by
    apply Subtype.ext
    apply Prod.ext
    · funext i l
      by_cases h : P (i,l)
      · simp [h, f.2 i l h]
      · simp [h]
    · rfl
  right_inv g := by
    apply Prod.ext
    · funext x
      rcases x with ⟨⟨i,l⟩,hx⟩
      simp [hx]
    · rfl

theorem zero_fresh_card (j : Nat) (P : Fin (j+1) × Bool → Prop) :
    Fintype.card {f : Fresh j // ∀ i l, P (i,l) → f.1 i l = false} =
      2 ^ (2*j+2 - Fintype.card {x : Fin (j+1) × Bool // P x}) * 2 := by
  rw [Fintype.card_congr (zeroFreshEquiv j P)]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_subtype_compl, Fintype.card_fin]
  congr 2
  omega
end BunDom
