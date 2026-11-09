import Reduction
import Mathlib.Data.Fin.Tuple.Sort
set_option autoImplicit false
set_option warningAsError true
namespace FloorSums
open Finset

theorem literal_permutation (m K : ℕ) (a : Fin 4 → ℕ) (e : Equiv.Perm (Fin 4)) :
    literalSum m K (a ∘ e) = literalSum m K a := by
  unfold literalSum
  apply sum_congr rfl
  intro j _
  apply sum_equiv e.finsetCongr
  · intro T
    simp
  · intro T _
    change (-1 : ℤ)^(4-T.card) * (((j+∑ i ∈ T, a (e i))/m : ℕ) : ℤ) =
      (-1 : ℤ)^(4-(T.map e.toEmbedding).card) *
        (((j+∑ i ∈ T.map e.toEmbedding, a i)/m : ℕ) : ℤ)
    rw [card_map, sum_map]
    rfl

theorem sorted_representative (m K : ℕ) (a : Fin 4 → ℕ) (ha : ∀ i, a i < m) :
    ∃ b : Fin 4 → ℕ, Monotone b ∧ (∀ i, b i < m) ∧
      literalSum m K b = literalSum m K a := by
  refine ⟨a ∘ Tuple.sort a, Tuple.monotone_sort a, ?_, literal_permutation m K a _⟩
  intro i
  exact ha _

/-- Exact remaining mathematical interface. This is a definition, not a theorem. -/
def SortedClampedBound : Prop := ∀ m H : ℕ, 0 < m → 1 ≤ H → H ≤ m →
  ∀ a : Fin 4 → ℕ, (∀ i, a i < m) → Monotone a →
  -3 * ((m/3 : ℕ) : ℤ) ≤ clampedSum m H a

/-- A conditional transfer only: no claim that its premise has been proved. -/
theorem endpoint_of_sorted_clamped_bound (h : SortedClampedBound) : LiteralEndpoint := by
  intro m hm a ha K hK
  obtain ⟨b, hb, hbm, he⟩ := sorted_representative m K a ha
  rw [← he, literal_eq_clamped m K b hm hbm hK]
  exact h m (K+1) hm (by omega) (by omega) b hbm hb

end FloorSums
