import Invariance
namespace EdgePattern
universe u v
open scoped BigOperators
variable {V : Type u} {W : Type v} {G : SimpleGraph V} {H : SimpleGraph W}

theorem edist_iso (e : G ≃g H) (x y : V) : H.edist (e x) (e y) = G.edist x y := by
  apply le_antisymm
  · change H.edist (e x) (e y) ≤ ⨅ p : G.Walk x y, (p.length : ℕ∞)
    apply le_iInf
    intro p
    simpa using (p.map e.toHom).edist_le
  · have h : G.edist (e.symm (e x)) (e.symm (e y)) ≤ H.edist (e x) (e y) := by
      change G.edist (e.symm (e x)) (e.symm (e y)) ≤ ⨅ p : H.Walk (e x) (e y), (p.length : ℕ∞)
      apply le_iInf
      intro p
      simpa using (p.map e.symm.toHom).edist_le
    simpa using h

theorem RootedIso.distance_eq {P : Rooted V} {Q : Rooted W} (e : RootedIso P Q) (x : V) :
    rootDistance Q (e.iso x) = rootDistance P x := by
  unfold rootDistance
  rw [← e.left_eq, ← e.right_eq, edist_iso, edist_iso]

theorem RootedIso.layer_map [Fintype V] [Fintype W] {P : Rooted V} {Q : Rooted W}
    (e : RootedIso P Q) (i : ℕ) :
    (layer P i).map e.iso.toEquiv.toEmbedding = layer Q i := by
  classical
  ext y
  obtain ⟨x, rfl⟩ := e.iso.surjective y
  simp only [Finset.mem_map, layer, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨z, hz, hzx⟩
    have he : z = x := e.iso.injective hzx
    subst z
    exact (e.distance_eq x).trans hz
  · intro hx
    exact ⟨x, (e.distance_eq x).symm.trans hx, rfl⟩

theorem maxima_map [Fintype V] [Fintype W] (e : G ≃g H) :
    (maxima G).map (Equiv.finsetCongr e.toEquiv).toEmbedding = maxima H := by
  classical
  ext s
  obtain ⟨t, rfl⟩ := (Equiv.finsetCongr e.toEquiv).surjective s
  simp only [Finset.mem_map, maxima, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
  constructor
  · rintro ⟨z, hz, hzt⟩
    have he : z = t := (Equiv.finsetCongr e.toEquiv).injective hzt
    subst z
    exact (maximum_map_iff e t).mpr hz
  · intro ht
    exact ⟨t, (maximum_map_iff e t).mp ht, rfl⟩

theorem RootedIso.expectation_eq [Fintype V] [Fintype W] {P : Rooted V} {Q : Rooted W}
    (e : RootedIso P Q) (i : ℕ) : expectation Q i = expectation P i := by
  classical
  unfold expectation
  rw [← maxima_map e.iso, Finset.card_map, Finset.sum_map]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  rw [← e.layer_map i]
  simp [Equiv.finsetCongr_apply, ← Finset.map_inter]
end EdgePattern
