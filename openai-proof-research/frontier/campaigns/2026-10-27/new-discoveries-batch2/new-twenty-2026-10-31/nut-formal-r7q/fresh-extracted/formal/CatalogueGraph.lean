import CheckedGraphIso
namespace Nut8
/-- A code has symmetric bits and no diagonal bits on the declared domain. -/
def SimpleCode (n code : ℕ) : Prop :=
  (∀ i : Fin n, graphBit n code i.val i.val = false) ∧
  ∀ i j : Fin n, graphBit n code i.val j.val = graphBit n code j.val i.val
instance (n code : ℕ) : Decidable (SimpleCode n code) := by
  unfold SimpleCode
  infer_instance

/-- A graph is defined even for malformed codes; `SimpleCode` removes the guards. -/
def catalogueGraph (n code : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ graphBit n code i.val j.val = true ∧ graphBit n code j.val i.val = true
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by simp⟩

instance (n code : ℕ) : DecidableRel (catalogueGraph n code).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem catalogueGraph_adj (n code : ℕ) (h : SimpleCode n code) (i j : Fin n) :
    (catalogueGraph n code).Adj i j ↔ graphBit n code i.val j.val = true := by
  constructor
  · exact fun ha => ha.2.1
  · intro hb
    refine ⟨?_, hb, ?_⟩
    · intro he
      subst j
      rw [h.1 i] at hb
      contradiction
    · rw [← h.2 i j]
      exact hb
end Nut8
