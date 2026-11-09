import ChordSanity
namespace Chord
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

def nested2 : Diagram 2 where
  partner i := ⟨3-i.val, by omega⟩
  involutive := by decide
  noFixed := by decide

theorem diagram_ext {n} (D E : Diagram n) (h : D.partner = E.partner) : D=E := by
  cases D
  cases E
  cases h
  rfl

theorem classify_one (D : Diagram 1) : D=one := by
  apply diagram_ext
  exact (by decide : ∀ t : Fin 2 → Fin 2,
    (∀ i, t (t i)=i) → (∀ i, t i ≠ i) → t=one.partner) D.partner D.involutive D.noFixed

theorem classify_two (D : Diagram 2) : D=u2 ∨ D=r2 ∨ D=nested2 := by
  have h := (by decide : ∀ t : Fin 4 → Fin 4,
    (∀ i, t (t i)=i) → (∀ i, t i ≠ i) →
    t=u2.partner ∨ t=r2.partner ∨ t=nested2.partner) D.partner D.involutive D.noFixed
  rcases h with h | h | h
  · exact Or.inl (diagram_ext _ _ h)
  · exact Or.inr (Or.inl (diagram_ext _ _ h))
  · exact Or.inr (Or.inr (diagram_ext _ _ h))

theorem range01_of_boundaries {n} (D : Diagram n)
    (hb : ∀ c, boundary D c = n ∨ boundary D c = n+2)
    (h0 : ∃ c, HasGenus D c 0) (h1 : ∃ c, HasGenus D c 1) : Range01 D := by
  intro g
  constructor
  · rintro ⟨c,hc⟩
    have := hb c
    unfold HasGenus at hc
    omega
  · rintro (rfl | rfl)
    · exact h0
    · exact h1

theorem one_range : Range01 one :=
  range01_of_boundaries one one_boundary_values (by decide) (by decide)

theorem u2_range : Range01 u2 :=
  range01_of_boundaries u2 u2_boundary_values (by decide) (by decide)

theorem r2_range : Range01 r2 :=
  range01_of_boundaries r2 r2_boundary_values (by decide) (by decide)

theorem nested2_range : Range01 nested2 :=
  range01_of_boundaries nested2 (by decide) (by decide) (by decide)

theorem GR_one (D : Diagram 1) : Range01 D := by
  rw [classify_one D]
  exact one_range

theorem GR_two (D : Diagram 2) : Range01 D := by
  rcases classify_two D with h | h | h <;> subst D
  · exact u2_range
  · exact r2_range
  · exact nested2_range

theorem not_range12_of_range01 {n} (D : Diagram n) (h : Range01 D) : ¬Range12 D := by
  intro hx
  have h0 : genusRange D 0 := (h 0).mpr (Or.inl rfl)
  have := (hx 0).mp h0
  omega

theorem literal_false_n1 (D : Diagram 1) : ¬Range12 D := not_range12_of_range01 D (GR_one D)
theorem literal_false_n2 (D : Diagram 2) : ¬Range12 D := not_range12_of_range01 D (GR_two D)
end Chord
