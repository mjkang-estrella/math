module
public import GridExceptionalPartitions
@[expose] public section
namespace Grid343536
open Finset
def relEquitable {V : Type*} [Fintype V] (F : SimpleGraph V)
    [DecidableRel F.Adj] (R : V → V → Prop) [DecidableRel R] : Prop :=
  ∀ u v, R u v → ∀ w,
    (univ.filter (fun x => F.Adj u x ∧ R x w)).card =
    (univ.filter (fun x => F.Adj v x ∧ R x w)).card
instance relEquitableDec {V : Type*} [Fintype V] (F : SimpleGraph V)
    [DecidableRel F.Adj] (R : V → V → Prop) [DecidableRel R] :
    Decidable (relEquitable F R) := by unfold relEquitable; infer_instance
instance block3Dec (a b : Fin 15) : DecidableRel (block3 a b).r :=
  fun _ _ => inferInstanceAs (Decidable (_ = _))
theorem relEquitable_iff {V : Type*} [Fintype V] (F : SimpleGraph V)
    [DecidableRel F.Adj] (r : Setoid V) [DecidableRel r.r] :
    relEquitable F r.r ↔ IsEquitable F r := by
  classical
  simp only [relEquitable, IsEquitable, Nat.card_eq_fintype_card, Fintype.card_subtype]
abbrev good3 := {ab : Fin 15 × Fin 15 // relEquitable (G 3 3) (block3 ab.1 ab.2).r}
theorem good3_card : Fintype.card good3 = 9 := by decide
theorem equitable3_card_le : Nat.card (EqPart (G 3 3)) ≤ 9 := by
  let f : good3 → EqPart (G 3 3) :=
    fun ab => ⟨block3 ab.val.1 ab.val.2, (relEquitable_iff _ _).mp ab.property⟩
  have hf : Function.Surjective f := by
    intro r
    obtain ⟨a,b,h⟩ := equitable3_complete r.val r.property
    refine ⟨⟨(a,b), ?_⟩, ?_⟩
    · apply (relEquitable_iff _ _).mpr
      rw [← h]
      exact r.property
    · apply Subtype.ext
      exact h.symm
  have h := Nat.card_le_card_of_surjective f hf
  simpa only [Nat.card_eq_fintype_card, good3_card] using h
end Grid343536
