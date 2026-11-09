import LiftFibres
noncomputable section
namespace XorMagic.EdgeTransport
variable {V : Type} {G : SimpleGraph V} (T : EdgeTransport G)

/-- Transport along a base walk, in the order in which its edges are traversed. -/
def along {u v : V} (p : G.Walk u v) : Four ≃ Four := by
  induction p with
  | nil => exact Equiv.refl Four
  | @cons u v w _h _p ih => exact (T.map u v).trans ih

theorem fibre_along (r : V × Four) {u v : V} (p : G.Walk u v) (x : Four) :
    x ∈ T.fibre r u ↔ T.along p x ∈ T.fibre r v := by
  induction p generalizing x with
  | nil => rfl
  | cons h p ih => exact (T.fibre_transport r h x).trans (ih _)

/-- Every base walk lifts from every starting point, with the computed endpoint. -/
theorem reachable_along {u v : V} (p : G.Walk u v) (x : Four) :
    T.graph.Reachable (u,x) (v,T.along p x) := by
  apply (T.mem_fibre (u,x) v _).mp
  exact (T.fibre_along (u,x) p x).mp ((T.mem_fibre _ _ _).mpr .rfl)

theorem along_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    T.along (p.append q) = (T.along p).trans (T.along q) := by
  induction p with
  | nil => apply Equiv.ext; intro x; rfl
  | cons h p ih => apply Equiv.ext; intro x; exact congrArg (fun e : Four ≃ Four => e (T.map _ _ x)) (ih q)

/-- A nontrivial affine loop excludes fibre size two at its base point. -/
theorem fibre_sizes_of_affine_loop (r : V × Four) {v : V} (p : G.Walk v v)
    (s : Bool) (c : Four) (h : ∀ x, T.along p x = affine s c x) :
    (T.fibre r v).card = 0 ∨ (T.fibre r v).card = 1 ∨
    (T.fibre r v).card = 3 ∨ (T.fibre r v).card = 4 := by
  apply invariant_fibre_sizes s c
  intro x
  simpa only [h] using T.fibre_along r p x
end XorMagic.EdgeTransport
