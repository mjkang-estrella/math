module
public import GridSideColors
@[expose] public section
namespace Grid343536

/-- MainOrbit transports with actual A0 conjugation, in both dimensions. -/
theorem main_orbit_transpose {m n : ℕ} (r : Setoid (Fin m × Fin n))
    (hr : IsEquitable (G m n) r)
    (h : ∀ s : Setoid (Fin n × Fin m), IsEquitable (G n m) s →
      s = orbitSetoid (G n m) (Hpi s)) :
    r = orbitSetoid (G m n) (Hpi r) := by
  let f := transpose m n
  let s := transportPartition f r
  have hs := h s (transport_equitable f r hr)
  apply le_antisymm
  · intro u v huv
    have huv' : s (f u) (f v) := by
      change r (f.symm (f u)) (f.symm (f v)); simpa using huv
    rw [hs] at huv'
    obtain ⟨g,hg,hgv⟩ := huv'
    exact ⟨transposeConj m n g,
      ⟨transposeConj_mem hg.1,conjugate_preserves_partition f r g hg.2⟩,
      conjugate_sends f g hgv⟩
  · exact Hpi_orbit_le r

/-- The entire ladder family in the other orientation. -/
theorem main_orbit_transposed_ladder (m : ℕ) (hm : 3 ≤ m)
    (r : Setoid (Fin m × Fin 2)) (hr : IsEquitable (G m 2) r) :
    r = orbitSetoid (G m 2) (Hpi r) :=
  main_orbit_transpose r hr (main_orbit_ladder m hm)

/-- Exact remaining geometric obligation. The exceptional 3×3 is already closed. -/
def OrdinaryBorderTransitivity : Prop :=
  ∀ m n : ℕ, 3 ≤ m → 3 ≤ n → ¬ (m = 3 ∧ n = 3) →
    ∀ r : Setoid (Fin m × Fin n), IsEquitable (G m n) r →
      ∀ u v, gridLayer u = 1 → r u v → ∃ g ∈ Hpi r, g u = v

theorem main_orbit_of_ordinary_border (border : OrdinaryBorderTransitivity) : MainOrbit := by
  intro m n hm hn r hr
  by_cases h1 : m = 1
  · subst m; exact main_orbit_row_path n hn r hr
  by_cases h2 : n = 1
  · subst n; exact main_orbit_column_path m hm r hr
  by_cases h3 : m = 2
  · subst m
    by_cases h4 : n = 2
    · subst n; exact main_orbit_two r hr
    · exact main_orbit_ladder n (by omega) r hr
  by_cases h4 : n = 2
  · subst n; exact main_orbit_transposed_ladder m (by omega) r hr
  have hm3 : 3 ≤ m := by omega
  have hn3 : 3 ≤ n := by omega
  by_cases hsmall : m = 3 ∧ n = 3
  · rcases hsmall with ⟨rfl,rfl⟩; exact main_orbit_three r hr
  apply positive_layer_propagation r hr gridLayer grid_layer_positive
    (grid_layer_invariant hm3 hn3 r hr)
  · intro g hg x; exact grid_layer_automorphism hm3 hn3 g x
  · exact grid_layer_step
  · exact border m n hm3 hn3 hsmall r hr
end Grid343536
namespace GridFinal5
open Grid343536
/-- Round 5 endpoint: still conditional on the exact ordinary-border obligation. -/
theorem mathdb_343536 (border : OrdinaryBorderTransitivity) :
    ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      (∀ r : Setoid (Fin m × Fin n),
        IsEquitable (G m n) r ↔
          ∃ H : Subgroup (G m n ≃g G m n), r = orbitSetoid (G m n) H) ∧
      (Nonempty (EqPart (G m n) ≃o Subgroup (G m n ≃g G m n)) ↔
        HasFreeVertex (G m n)) ∧
      (HasFreeVertex (G m n) ↔ ¬ (2 ≤ m ∧ m = n ∧ n ≤ 3)) :=
  GridFinal4.mathdb_343536 (main_orbit_of_ordinary_border border)
end GridFinal5
