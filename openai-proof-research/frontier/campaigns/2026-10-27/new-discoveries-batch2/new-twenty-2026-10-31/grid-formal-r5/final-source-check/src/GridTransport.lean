module
public import GridDeterminism
@[expose] public section
namespace Grid343536

/-- Transport a partition in the direction of a graph isomorphism. -/
def transportPartition {V W : Type*} {G : SimpleGraph V} {F : SimpleGraph W}
    (f : G ≃g F) (r : Setoid V) : Setoid W := Setoid.comap f.symm r

theorem transport_equitable {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {F : SimpleGraph W} (f : G ≃g F) (r : Setoid V)
    (hr : IsEquitable G r) : IsEquitable F (transportPartition f r) := by
  intro u v huv w
  have hc (z : W) :
      Nat.card {x // F.Adj z x ∧ (transportPartition f r) x w} =
        Nat.card {x // G.Adj (f.symm z) x ∧ r x (f.symm w)} := by
    apply Nat.card_congr
    exact {
      toFun := fun x => ⟨f.symm x, f.symm.map_rel_iff.mpr x.property.1, x.property.2⟩
      invFun := fun x => ⟨f x, by simpa using f.map_rel_iff.mpr x.property.1,
        by change r (f.symm (f x)) (f.symm w); simpa using x.property.2⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro x; apply Subtype.ext; simp }
  rw [hc u, hc v]
  exact hr _ _ huv _

/-- Conjugating a colour-preserving map back preserves the original partition. -/
theorem conjugate_preserves_partition {V W : Type*} {G : SimpleGraph V}
    {F : SimpleGraph W} (f : G ≃g F) (r : Setoid V) (g : F ≃g F)
    (hg : ∀ x, (transportPartition f r) (g x) x) :
    ∀ x, r ((f.trans g).trans f.symm x) x := by
  intro x
  have h := hg (f x)
  change r (f.symm (g (f x))) (f.symm (f x)) at h
  simpa using h

/-- The actual endpoint map in the WLOG conjugation step. -/
theorem conjugate_sends {V W : Type*} {G : SimpleGraph V}
    {F : SimpleGraph W} (f : G ≃g F) (g : F ≃g F) {u v : V}
    (h : g (f u) = f v) : ((f.trans g).trans f.symm) u = v := by
  change f.symm (g (f u)) = v
  rw [h]
  simp
end Grid343536
