import Endpoint
namespace IR350452
open Finset
instance : DecidableRel (SimpleGraph.pathGraph 2).Adj := by
  intro a b
  exact decidable_of_iff (a.val + 1 = b.val ∨ b.val + 1 = a.val) SimpleGraph.pathGraph_adj.symm
instance (D : Finset (Fin 2)) : Decidable (Irredundant (SimpleGraph.pathGraph 2) D) := by
  unfold Irredundant IsPrivateNbr
  infer_instance
instance (A B : Finset (Fin 2)) : Decidable (Swap (SimpleGraph.pathGraph 2) A B) := by
  unfold Swap
  infer_instance
lemma k2_max : ∀ D : Finset (Fin 2),
    (Irredundant (SimpleGraph.pathGraph 2) D ∧
      ∀ E, Irredundant (SimpleGraph.pathGraph 2) E → E.card ≤ D.card) ↔
      ∃ i : Fin 2, D = {i} := by decide

def controlToIR (i : Fin 2) : {D // IRSet (SimpleGraph.pathGraph 2) D} :=
  ⟨{i}, (irSet_iff_max _ _).mpr ((k2_max _).mpr ⟨i, rfl⟩)⟩
lemma control_bijective : Function.Bijective controlToIR := by
  constructor
  · intro i j h
    have hh : ({i} : Finset (Fin 2)) = {j} := congrArg Subtype.val h
    simpa using hh
  · rintro ⟨D, hD⟩
    obtain ⟨i, rfl⟩ := (k2_max D).mp ((irSet_iff_max _ _).mp hD)
    exact ⟨i, rfl⟩
noncomputable def controlIso : SimpleGraph.pathGraph 2 ≃g IRGraph (SimpleGraph.pathGraph 2) where
  toEquiv := Equiv.ofBijective controlToIR control_bijective
  map_rel_iff' := by
    intro i j
    change Swap (SimpleGraph.pathGraph 2) {i} {j} ↔ (SimpleGraph.pathGraph 2).Adj i j
    revert i j
    decide

theorem nonvacuity : IsIRGraph (SimpleGraph.pathGraph 2) :=
  ⟨Fin 2, inferInstance, inferInstance, SimpleGraph.pathGraph 2, ⟨controlIso⟩⟩
end IR350452
