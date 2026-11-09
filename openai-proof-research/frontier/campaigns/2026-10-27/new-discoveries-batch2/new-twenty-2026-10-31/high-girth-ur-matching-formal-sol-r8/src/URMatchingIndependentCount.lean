module
public import URMatchingBase
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.BigOperators
@[expose] public section
namespace URMatching
universe u
/-- The full product space: independent colors, with no graph-goodness restriction. -/
abbrev PermutationTuples (N d : ℕ) := Fin d → Equiv.Perm (Fin N)

def AvoidsRectangle {N : ℕ} (A B : Finset (Fin N)) (σ : Equiv.Perm (Fin N)) : Prop :=
  ∀ x ∈ A, σ x ∉ B

/-- Exact finite independence counting for arbitrary coordinate predicates. -/
def coordinateEventEquiv {Ω : Type u} (d : ℕ) (E : Ω → Prop) :
    {f : Fin d → Ω // ∀ c, E (f c)} ≃ (Fin d → {x : Ω // E x}) where
  toFun f c := ⟨f.val c, f.property c⟩
  invFun g := ⟨fun c => (g c).val, fun c => (g c).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem coordinate_event_card {Ω : Type u} [Fintype Ω] (d : ℕ) (E : Ω → Prop)
    [DecidablePred E] :
    Fintype.card {f : Fin d → Ω // ∀ c, E (f c)} =
      (Fintype.card {x : Ω // E x}) ^ d := by
  rw [Fintype.card_congr (coordinateEventEquiv d E), Fintype.card_fun, Fintype.card_fin]

open scoped Classical in
/-- For the actual 100 independent bijections, the fixed-rectangle avoidance count
is exactly the one-color count to the 100th power. No conditioning is used. -/
theorem hundred_color_avoidance_count (N : ℕ) (A B : Finset (Fin N)) :
    Fintype.card {f : PermutationTuples N 100 // ∀ c, AvoidsRectangle A B (f c)} =
      (Fintype.card {σ : Equiv.Perm (Fin N) // AvoidsRectangle A B σ}) ^ 100 := by
  classical
  exact coordinate_event_card 100 (AvoidsRectangle A B)
end URMatching
