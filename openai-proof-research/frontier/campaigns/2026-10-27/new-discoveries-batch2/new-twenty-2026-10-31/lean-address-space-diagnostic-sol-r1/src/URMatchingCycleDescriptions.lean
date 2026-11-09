module
public import URMatchingPrescriptions
@[expose] public section
namespace URMatching
open scoped Classical
/-- Ordered cycle descriptions with two distinct vertex lists and arbitrary colours.
Index k encodes half-length k+1; at k=0 valid descriptions require distinct colours. -/
abbrev CycleDescription (N k : ℕ) :=
  (Fin (k+1) ↪ Fin N) × (Fin (k+1) ↪ Fin N) ×
    (Fin (k+1) → Fin 100) × (Fin (k+1) → Fin 100)

def ValidDescription {N k : ℕ} (w : CycleDescription N k) : Prop :=
  k = 0 → w.2.2.1 0 ≠ w.2.2.2 0

/-- The two edges at each Y vertex, with cyclically consecutive X vertices. -/
def DescriptionOccurs {N k : ℕ} (w : CycleDescription N k)
    (σ : PermutationTuples N 100) : Prop :=
  ∀ i : Fin (k+1), σ (w.2.2.1 i) (w.1 i) = w.2.1 i ∧
    σ (w.2.2.2 i) (w.1 (i+1)) = w.2.1 i

noncomputable def descriptionEncoding (N k : ℕ) : CycleDescription N k →
    (Fin (k+1) → Fin N) × (Fin (k+1) → Fin N) ×
      (Fin (k+1) → Fin 100) × (Fin (k+1) → Fin 100) :=
  fun w => (w.1, w.2.1, w.2.2.1, w.2.2.2)

theorem descriptionEncoding_injective (N k : ℕ) :
    Function.Injective (descriptionEncoding N k) := by
  intro a b h
  obtain ⟨a₁,a₂,a₃,a₄⟩ := a
  obtain ⟨b₁,b₂,b₃,b₄⟩ := b
  simp only [descriptionEncoding, Prod.mk.injEq] at h
  obtain ⟨h₁,h₂,h₃,h₄⟩ := h
  have e₁ : a₁ = b₁ := DFunLike.coe_injective h₁
  have e₂ : a₂ = b₂ := DFunLike.coe_injective h₂
  exact e₁ ▸ e₂ ▸ h₃ ▸ h₄ ▸ rfl

/-- Ordered witness enumeration bound. The validity restriction only reduces it. -/
theorem description_count_bound (N k : ℕ) :
    Fintype.card {w : CycleDescription N k // ValidDescription w} ≤
      N ^ (k+1) * (N ^ (k+1) * (100 ^ (k+1) * 100 ^ (k+1))) := by
  classical
  calc
    _ ≤ Fintype.card (CycleDescription N k) := Fintype.card_subtype_le _
    _ ≤ Fintype.card ((Fin (k+1) → Fin N) × (Fin (k+1) → Fin N) ×
        (Fin (k+1) → Fin 100) × (Fin (k+1) → Fin 100)) :=
      Fintype.card_le_of_injective _ (descriptionEncoding_injective N k)
    _ = _ := by simp
end URMatching
