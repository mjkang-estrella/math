module
public import GridExceptionalCounts
public import GridExceptionalTwo
@[expose] public section
namespace Grid343536
instance block2Dec (a : Fin 15) : DecidableRel (block2 a).r :=
  fun _ _ => inferInstanceAs (Decidable (_ = _))
abbrev good2 := {a : Fin 15 // relEquitable (G 2 2) (block2 a).r}
theorem good2_card : Fintype.card good2 = 7 := by decide
theorem equitable2_card_le : Nat.card (EqPart (G 2 2)) ≤ 7 := by
  let f : good2 → EqPart (G 2 2) :=
    fun a => ⟨block2 a.val, (relEquitable_iff _ _).mp a.property⟩
  have hf : Function.Surjective f := by
    intro r
    obtain ⟨a,h⟩ := equitable2_complete r.val
    refine ⟨⟨a, ?_⟩, ?_⟩
    · apply (relEquitable_iff _ _).mpr
      rw [← h]
      exact r.property
    · apply Subtype.ext
      exact h.symm
  have h := Nat.card_le_card_of_surjective f hf
  simpa only [Nat.card_eq_fintype_card, good2_card] using h
end Grid343536
