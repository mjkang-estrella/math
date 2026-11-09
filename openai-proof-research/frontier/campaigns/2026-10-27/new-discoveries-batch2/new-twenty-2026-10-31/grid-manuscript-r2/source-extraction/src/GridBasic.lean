module
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Order.Group.End
public import Mathlib.Order.Hom.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Setoid.Partition

open SimpleGraph Finset
@[expose] public section

namespace Grid343536
abbrev G (m n : ℕ) := (pathGraph m).boxProd (pathGraph n)

def IsEquitable {V : Type*} [Fintype V] (G : SimpleGraph V) (r : Setoid V) : Prop :=
  ∀ u v, r u v → ∀ w,
    Nat.card {x // G.Adj u x ∧ r x w} = Nat.card {x // G.Adj v x ∧ r x w}

abbrev EqPart {V : Type*} [Fintype V] (G : SimpleGraph V) :=
  {r : Setoid V // IsEquitable G r}

def orbitSetoid {V : Type*} (G : SimpleGraph V) (H : Subgroup (G ≃g G)) : Setoid V where
  r u v := ∃ g ∈ H, g u = v
  iseqv := by
    refine ⟨fun u => ⟨1, H.one_mem, rfl⟩, ?_, ?_⟩
    · rintro u v ⟨g, hg, rfl⟩
      exact ⟨g⁻¹, H.inv_mem hg, by simp⟩
    · rintro u v w ⟨g, hg, rfl⟩ ⟨k, hk, rfl⟩
      exact ⟨k * g, H.mul_mem hk hg, rfl⟩

def HasFreeVertex {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ x : V, ∀ g : G ≃g G, g x = x → g = 1

theorem orbit_equitable {V : Type*} [Fintype V] (G : SimpleGraph V)
    (H : Subgroup (G ≃g G)) : IsEquitable G (orbitSetoid G H) := by
  rintro u v ⟨g, hg, rfl⟩ w
  let e : {x // G.Adj u x ∧ (orbitSetoid G H) x w} ≃
      {x // G.Adj (g u) x ∧ (orbitSetoid G H) x w} :=
    { toFun := fun x => ⟨g x, g.map_rel_iff.mpr x.property.1, by
        obtain ⟨k, hk, hkw⟩ := x.property.2
        exact ⟨k * g⁻¹, H.mul_mem hk (H.inv_mem hg), by simpa using hkw⟩⟩
      invFun := fun x => ⟨g⁻¹ x, by simpa using (g⁻¹).map_rel_iff.mpr x.property.1, by
        obtain ⟨k, hk, hkw⟩ := x.property.2
        exact ⟨k * g, H.mul_mem hk hg, by simpa using hkw⟩⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro x; apply Subtype.ext; simp }
  exact Nat.card_congr e

def orbitMap {V : Type*} [Fintype V] (G : SimpleGraph V)
    (H : Subgroup (G ≃g G)) : EqPart G :=
  ⟨orbitSetoid G H, orbit_equitable G H⟩

theorem orbitMap_mono {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Monotone (orbitMap G) := by
  intro H K h u v huv
  obtain ⟨g, hg, hgv⟩ := huv
  exact ⟨g, h hg, hgv⟩

theorem orbitMap_reflects {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hf : HasFreeVertex G) (H K : Subgroup (G ≃g G)) :
    orbitMap G H ≤ orbitMap G K ↔ H ≤ K := by
  refine ⟨?_, fun h => orbitMap_mono G h⟩
  obtain ⟨x, hx⟩ := hf
  intro h g hg
  obtain ⟨k, hk, hkg⟩ := h (show (orbitSetoid G H) x (g x) from ⟨g, hg, rfl⟩)
  have he : k⁻¹ * g = 1 := hx _ (by
    change k⁻¹ (g x) = x
    rw [← hkg]
    simp)
  have : g = k := by
    have := congrArg (fun a => k * a) he
    simpa [mul_assoc] using this
  simpa [this] using hk

noncomputable def naturalIso {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hf : HasFreeVertex G) (hs : Function.Surjective (orbitMap G)) :
    Subgroup (G ≃g G) ≃o EqPart G :=
  { toEquiv := Equiv.ofBijective (orbitMap G)
      ⟨fun H K h => le_antisymm ((orbitMap_reflects G hf H K).mp (le_of_eq h))
        ((orbitMap_reflects G hf K H).mp (le_of_eq h.symm)), hs⟩
    map_rel_iff' := fun {H K} => orbitMap_reflects G hf H K }

theorem grid_adj_iff {m n : ℕ} (x y : Fin m × Fin n) :
    (G m n).Adj x y ↔
    (x.1 = y.1 ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)) ∨
    ((x.1.val + 1 = y.1.val ∨ y.1.val + 1 = x.1.val) ∧ x.2 = y.2) := by
  simp only [G, boxProd_adj, pathGraph_adj]
  tauto
instance gridDecAdj (m n : ℕ) : DecidableRel (G m n).Adj :=
  fun x y => decidable_of_iff _ (grid_adj_iff x y).symm
end Grid343536
