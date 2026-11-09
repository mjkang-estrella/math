import Four
import TranslationCardinality
namespace XorMagic

theorem translation_exists_four (m e : ℕ) (hedge : 2*m ≤ e)
    (D : (Fin m → Four) →+ (Fin e → Four))
    (B : (Fin e → Four) →+ (Fin m → Four))
    (nonzero : ∃ a, B (D a) ≠ 0) :
    ∃ c : Fin e → Four, B c = 0 ∧ c ∉ D.range := by
  apply translation_exists D B ?_ nonzero
  have fourcard : Fintype.card Four = 4 := by decide
  simp only [Fintype.card_fun, Fintype.card_fin, fourcard]
  rw [← pow_add]
  exact Nat.pow_le_pow_right (by decide) (by omega)
end XorMagic
