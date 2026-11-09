import Nut
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
namespace Nut8
variable {V : Type} [Fintype V]

/-- Automorphisms represented as a subgroup of vertex permutations. -/
def graphPerms (G : SimpleGraph V) : Subgroup (Equiv.Perm V) where
  carrier := {σ | ∀ v w, G.Adj (σ v) (σ w) ↔ G.Adj v w}
  one_mem' := by intro v w; rfl
  mul_mem' := by
    intro σ τ hσ hτ v w
    exact (hσ (τ v) (τ w)).trans (hτ v w)
  inv_mem' := by
    intro σ hσ v w
    exact (by simpa using (hσ (σ⁻¹ v) (σ⁻¹ w)).symm)

/-- Orbits under every member of a subgroup, without a chosen generator. -/
def subgroupOrbitSetoid (H : Subgroup (Equiv.Perm V)) : Setoid V where
  r v w := ∃ σ ∈ H, σ v = w
  iseqv := ⟨fun v => ⟨1, H.one_mem, rfl⟩,
    by
      rintro v w ⟨σ,hσ,rfl⟩
      exact ⟨σ⁻¹, H.inv_mem hσ, σ.symm_apply_apply v⟩,
    by
      rintro v w x ⟨σ,hσ,rfl⟩ ⟨τ,hτ,rfl⟩
      exact ⟨τ*σ, H.mul_mem hτ hσ, rfl⟩⟩

omit [Fintype V] in
lemma subgroupOrbit_zpowers (σ : Equiv.Perm V) :
    subgroupOrbitSetoid (Subgroup.zpowers σ) = orbitSetoid σ := by
  apply Setoid.ext
  intro v w
  constructor
  · rintro ⟨τ,hτ,hvw⟩
    obtain ⟨n,rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
    exact ⟨n,hvw⟩
  · rintro ⟨n,hn⟩
    exact ⟨σ^n, (Subgroup.zpowers σ).zpow_mem (Subgroup.mem_zpowers σ) n, hn⟩

/-- The manuscript's cyclic-group definition with literal subgroup orbits. -/
def CyclicGroupCirculant (l : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ H : Subgroup (Equiv.Perm V), IsCyclic H ∧ H ≤ graphPerms G ∧
    Nat.card (Quotient (subgroupOrbitSetoid H)) = l ∧
    ∃ m : ℕ, ∀ v, Nat.card {w // (subgroupOrbitSetoid H).r v w} = m

/-- The source's cyclic subgroup and the inherited chosen-generator formulation agree. -/
theorem cyclicGroupCirculant_iff (l : ℕ) (G : SimpleGraph V) :
    CyclicGroupCirculant l G ↔ Circulant l G := by
  classical
  have hcard (σ : Equiv.Perm V) (v : V) :
      Nat.card {w // (orbitSetoid σ).r v w} = (orbitFinset σ v).card := by
    change Nat.card {w // σ.SameCycle v w} = _
    simp_rw [← mem_orbitFinset]
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  constructor
  · rintro ⟨H,hcyc,hG,hq,m,hm⟩
    obtain ⟨σ,rfl⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top H).mp hcyc
    have hσ : σ ∈ graphPerms G := hG (Subgroup.mem_zpowers σ)
    change ∀ v w, G.Adj (σ v) (σ w) ↔ G.Adj v w at hσ
    let f : G ≃g G := ⟨σ,fun {_ _} => hσ _ _⟩
    rw [subgroupOrbit_zpowers] at hq hm
    exact ⟨f,hq,m,fun v => (hcard σ v).symm.trans (hm v)⟩
  · rintro ⟨σ,hq,m,hm⟩
    refine ⟨Subgroup.zpowers σ.toEquiv, inferInstance, ?_, ?_, m, ?_⟩
    · exact Subgroup.zpowers_le.mpr (fun _ _ => σ.map_adj_iff)
    · simpa only [subgroupOrbit_zpowers] using hq
    · intro v
      rw [subgroupOrbit_zpowers, hcard]
      exact hm v
end Nut8
