module
public import URMatchingCycleDescriptions
@[expose] public section
namespace URMatching
open scoped Classical
def slotColour {N k : ℕ} (w : CycleDescription N k) (s : Bool × Fin (k+1)) : Fin 100 :=
  if s.1 then w.2.2.2 s.2 else w.2.2.1 s.2
def slotInput {N k : ℕ} (w : CycleDescription N k) (s : Bool × Fin (k+1)) : Fin N :=
  if s.1 then w.1 (s.2+1) else w.1 s.2

theorem slot_occurs {N k : ℕ} (w : CycleDescription N k)
    (τ : PermutationTuples N 100) (hτ : DescriptionOccurs w τ)
    (s : Bool × Fin (k+1)) : τ (slotColour w s) (slotInput w s) = w.2.1 s.2 := by
  obtain ⟨b,i⟩ := s
  cases b
  · exact (hτ i).1
  · exact (hτ i).2

theorem cyclic_next_ne {k : ℕ} (hk : k ≠ 0) (i : Fin (k+1)) : i+1 ≠ i := by
  intro h
  have ilast : i = Fin.last k := Fin.add_one_le_iff.mp (Fin.le_of_eq h)
  have e : (0 : Fin (k+1)) = Fin.last k := by simpa only [ilast, Fin.last_add_one] using h
  exact hk (congrArg Fin.val e).symm

theorem slots_injective {N k : ℕ} (w : CycleDescription N k)
    (hw : ValidDescription w) (τ : PermutationTuples N 100) (hτ : DescriptionOccurs w τ) :
    Function.Injective (fun s : Bool × Fin (k+1) => (slotColour w s, slotInput w s)) := by
  intro s t h
  have hc := congrArg Prod.fst h
  have hx := congrArg Prod.snd h
  change slotColour w s = slotColour w t at hc
  change slotInput w s = slotInput w t at hx
  have hy : w.2.1 s.2 = w.2.1 t.2 := by
    rw [← slot_occurs w τ hτ s, ← slot_occurs w τ hτ t, hc, hx]
  have hi := w.2.1.injective hy
  obtain ⟨b,i⟩ := s
  obtain ⟨d,j⟩ := t
  change i = j at hi
  subst j
  cases b <;> cases d
  · rfl
  · simp only [slotInput, Bool.false_eq_true, ↓reduceIte, slotColour] at hc hx
    by_cases hk : k = 0
    · subst k
      have iz : i = 0 := Fin.fin_one_eq_zero i
      exact False.elim (hw rfl (iz ▸ hc))
    · exact False.elim (cyclic_next_ne hk i (w.1.injective hx).symm)
  · simp only [slotInput, Bool.false_eq_true, ↓reduceIte, slotColour] at hc hx
    by_cases hk : k = 0
    · subst k
      have iz : i = 0 := Fin.fin_one_eq_zero i
      exact False.elim (hw rfl (iz ▸ hc.symm))
    · exact False.elim (cyclic_next_ne hk i (w.1.injective hx))
  · rfl
end URMatching
