module
public import GridFinal
@[expose] public section
namespace Grid343536

/-- Matching neighbours exist in every cell that meets a neighbourhood. -/
theorem matching_neighbor {V : Type*} [Fintype V] {G : SimpleGraph V}
    {r : Setoid V} (hr : IsEquitable G r) {u v a : V}
    (huv : r u v) (hua : G.Adj u a) :
    ∃ b, G.Adj v b ∧ r b a := by
  have h := hr u v huv a
  have hp : 0 < Nat.card {x // G.Adj u x ∧ r x a} :=
    Nat.card_pos_iff.mpr ⟨⟨⟨a, hua, r.refl a⟩⟩, inferInstance⟩
  rw [h] at hp
  obtain ⟨⟨b⟩, _⟩ := (Nat.card_pos_iff.mp hp)
  exact ⟨b.val, b.property⟩

/-- Positive-layer propagation, including the necessary positivity premise. -/
theorem positive_layer_propagation {m n : ℕ} (r : Setoid (Fin m × Fin n))
    (hr : IsEquitable (G m n) r) (lay : Fin m × Fin n → ℕ)
    (hpos : ∀ x, 1 ≤ lay x)
    (hinv : ∀ x y, r x y → lay x = lay y)
    (hA0 : ∀ g ∈ A0 m n, ∀ x, lay (g x) = lay x)
    (hstep : ∀ w, 2 ≤ lay w → ∃ a, (G m n).Adj w a ∧ lay a + 1 = lay w ∧
      ∀ b, (G m n).Adj a b → lay w ≤ lay b → b = w)
    (hbase : ∀ u v, lay u = 1 → r u v → ∃ g ∈ Hpi r, g u = v) :
    r = orbitSetoid (G m n) (Hpi r) := by
  apply le_antisymm
  · intro u v huv
    have key : ∀ k, ∀ u v, lay u = k → r u v → ∃ g ∈ Hpi r, g u = v := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        intro u v hu huv
        by_cases hk : k = 1
        · exact hbase u v (hu.trans hk) huv
        have htwo : 2 ≤ lay u := by have := hpos u; omega
        obtain ⟨a, hua, hla, huniq⟩ := hstep u htwo
        obtain ⟨b, hvb, hba⟩ := matching_neighbor hr huv hua
        obtain ⟨g, hg, hgab⟩ := ih (lay a) (by omega) a b rfl (r.symm hba)
        refine ⟨g, hg, ?_⟩
        have hgv : g⁻¹ v = u := huniq (g⁻¹ v) (by
          have h := (g⁻¹).map_rel_iff.mpr hvb.symm
          simpa [← hgab] using h) (by
          rw [hA0 _ (Subgroup.inv_mem _ hg.1) v, ← hinv u v huv])
        have := congrArg (fun x => g x) hgv
        simpa using this.symm
    exact key (lay u) u v rfl huv
  · exact Hpi_orbit_le r

/-- Cell-saturated sets remain saturated after taking the neighbour-existence preimage. -/
theorem saturated_neighbor_preimage {V : Type*} [Fintype V] {G : SimpleGraph V}
    {r : Setoid V} (hr : IsEquitable G r) {S : Set V}
    (hS : ∀ x y, r x y → (x ∈ S ↔ y ∈ S)) {u v : V} (huv : r u v) :
    (∃ a ∈ S, G.Adj u a) ↔ ∃ b ∈ S, G.Adj v b := by
  have key : ∀ u v, r u v → (∃ a ∈ S, G.Adj u a) → ∃ b ∈ S, G.Adj v b := by
    rintro u v huv ⟨a, ha, hua⟩
    obtain ⟨b, hvb, hba⟩ := matching_neighbor hr huv hua
    exact ⟨b, (hS b a hba).mpr ha, hvb⟩
  exact ⟨key u v huv, key v u (r.symm huv)⟩
end Grid343536
