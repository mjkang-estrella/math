import Matching
noncomputable section
namespace UnitCoset
variable {G : Type*} [AddCommGroup G] [DecidableEq G] {A B : Finset G}

theorem positive_iff (f : A ≃ B) (x : G) :
    0 < multiplicity f x ↔ x ∈ support f := by
  simp only [multiplicity, support, Finset.card_pos, Finset.Nonempty, Finset.mem_filter,
    Finset.mem_image, Finset.mem_univ, true_and]

theorem unit_iff_positive (f : A ≃ B) :
    UnitSequence f ↔ ∀ x, 0 < multiplicity f x → multiplicity f x = 1 := by
  simp only [UnitSequence, sequence, Multiset.mem_sort, Multiset.mem_map,
    Finset.mem_val]
  constructor
  · intro h x hx
    exact h _ ⟨x, (positive_iff f x).mp hx, rfl⟩
  · intro h n hn
    obtain ⟨x, hx, rfl⟩ := hn
    exact h x ((positive_iff f x).mpr hx)

theorem unit_iff_injective (f : A ≃ B) :
    UnitSequence f ↔ Function.Injective (sumMap f) := by
  rw [unit_iff_positive]
  constructor
  · intro h a b hab
    have ha : a ∈ Finset.univ.filter (fun z : A => sumMap f z = sumMap f a) := by simp
    have hb : b ∈ Finset.univ.filter (fun b : A => sumMap f b = sumMap f a) := by simp [hab]
    have hc := h (sumMap f a) (Finset.card_pos.mpr ⟨a, ha⟩)
    exact Finset.card_le_one.mp hc.le a ha b hb
  · intro h x hx
    apply Nat.le_antisymm
    · apply Finset.card_le_one.mpr
      intro a ha b hb
      exact h ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
    · exact hx

theorem multiplicity_one (f : A ≃ B) (hi : Function.Injective (sumMap f))
    (a : A) : multiplicity f (sumMap f a) = 1 :=
  (unit_iff_positive f).mp ((unit_iff_injective f).mpr hi) _
    (Finset.card_pos.mpr ⟨a, by simp⟩)

theorem multiplicity_zero (f : A ≃ B) (x : G)
    (h : ∀ a, sumMap f a ≠ x) : multiplicity f x = 0 := by
  simp only [multiplicity, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a _
  exact h a

-- Finite source sets have exactly the Finset representation used here.
omit [AddCommGroup G] [DecidableEq G] in
theorem finite_set_bridge (S : Set G) (h : S.Finite) :
    ∃ A : Finset G, (A : Set G) = S := ⟨h.toFinset, h.coe_toFinset⟩
end UnitCoset
