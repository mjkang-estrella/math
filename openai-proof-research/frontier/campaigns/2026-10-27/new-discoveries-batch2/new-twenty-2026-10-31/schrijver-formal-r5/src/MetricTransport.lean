import MaskSemantics
namespace Schrijver
set_option autoImplicit false

theorem iso_connected {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β}
    (e : G ≃g H) (hc : G.Connected) : H.Connected := e.connected_iff.mp hc

theorem iso_dist {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β}
    (e : G ≃g H) (hc : G.Connected) (a b : α) : H.dist (e a) (e b) = G.dist a b := by
  have hd := iso_connected e hc
  apply Nat.le_antisymm
  · obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist a b
    exact (SimpleGraph.dist_le (p.map e.toHom)).trans_eq (by simpa using hp)
  · obtain ⟨p, hp⟩ := hd.exists_walk_length_eq_dist (e a) (e b)
    have hh := SimpleGraph.dist_le (p.map e.symm.toHom)
    change G.dist (e.symm (e a)) (e.symm (e b)) ≤ (p.map e.symm.toHom).length at hh
    simpa only [SimpleGraph.Walk.length_map, e.symm_apply_apply, hp] using hh

theorem iso_walk_bound {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β}
    (e : G ≃g H) {d : ℕ}
    (hb : ∀ a b, ∃ p : G.Walk a b, p.length ≤ d) :
    ∀ a b, ∃ p : H.Walk a b, p.length ≤ d := by
  intro a b
  obtain ⟨a, rfl⟩ := e.toEquiv.surjective a
  obtain ⟨b, rfl⟩ := e.toEquiv.surjective b
  obtain ⟨p, hp⟩ := hb a b
  exact ⟨p.map e.toHom, by simpa using hp⟩

-- Covers the precise use of symmetry in the upper certificate.
theorem orbit_walk_bound {α : Type*} {G : SimpleGraph α} {d : ℕ} (roots : Set α)
    (trees : ∀ r ∈ roots, ∀ v, ∃ p : G.Walk v r, p.length ≤ d)
    (cover : ∀ a, ∃ (e : G ≃g G), ∃ r, r ∈ roots ∧ e a = r) :
    ∀ a b, ∃ p : G.Walk a b, p.length ≤ d := by
  intro a b
  obtain ⟨e, r, hr, he⟩ := cover a
  obtain ⟨p, hp⟩ := trees r hr (e b)
  subst r
  let q : G.Walk (e.symm (e a)) (e.symm (e b)) := p.reverse.map e.symm.toHom
  have hq : q.length ≤ d := by simpa [q] using hp
  have hh : ∃ p : G.Walk (e.symm (e a)) (e.symm (e b)), p.length ≤ d := ⟨q, hq⟩
  rw [show e.symm (e a) = a from e.toEquiv.symm_apply_apply a,
    show e.symm (e b) = b from e.toEquiv.symm_apply_apply b] at hh
  exact hh
end Schrijver
