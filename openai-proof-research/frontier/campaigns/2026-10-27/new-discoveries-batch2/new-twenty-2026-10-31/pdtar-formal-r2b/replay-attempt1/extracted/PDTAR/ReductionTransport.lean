import PDTAR.Remaining
namespace PDTAR
set_option linter.unusedSectionVars false
open Finset
variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Pull adjacency back along a vertex equivalence. -/
def reductionPull (e : V ≃ W) (H : SimpleGraph W) : SimpleGraph V := H.comap e

@[simp] theorem reductionPull_adj (e : V ≃ W) (H : SimpleGraph W) (x y : V) :
    (reductionPull e H).Adj x y ↔ H.Adj (e x) (e y) := Iff.rfl

theorem reduction_closed_transport (e : V ≃ W) (H : SimpleGraph W) (S : Finset V) :
    (closed (reductionPull e H) S).map e.toEmbedding = closed H (S.map e.toEmbedding) := by
  ext y
  obtain ⟨x,rfl⟩ := e.surjective y
  simp only [mem_map_equiv, Equiv.symm_apply_apply, mem_closed, reductionPull_adj]
  constructor
  · rintro (hs | ⟨v,hv,ha⟩)
    · exact .inl hs
    · exact .inr ⟨e v, by simpa using hv,ha⟩
  · rintro (hs | ⟨v,hv,ha⟩)
    · exact .inl hs
    · obtain ⟨u,rfl⟩ := e.surjective v
      exact .inr ⟨u,by simpa using hv,ha⟩

theorem reduction_step_transport (e : V ≃ W) (H : SimpleGraph W) (S : Finset V) :
    (step (reductionPull e H) S).map e.toEmbedding = step H (S.map e.toEmbedding) := by
  ext y
  obtain ⟨x,rfl⟩ := e.surjective y
  simp only [mem_map_equiv, Equiv.symm_apply_apply, mem_step, reductionPull_adj]
  constructor
  · rintro (hs | ⟨v,hv,ha,hu⟩)
    · exact .inl hs
    · right
      refine ⟨e v,by simpa using hv,ha,?_⟩
      intro w hw hn
      obtain ⟨z,rfl⟩ := e.surjective w
      exact congrArg e (hu z hw (by simpa using hn))
  · rintro (hs | ⟨v,hv,ha,hu⟩)
    · exact .inl hs
    · obtain ⟨u,rfl⟩ := e.surjective v
      right
      refine ⟨u,by simpa using hv,ha,?_⟩
      intro w hw hn
      exact e.injective (hu (e w) hw (by simpa using hn))

theorem reduction_propagate_transport (e : V ≃ W) (H : SimpleGraph W)
    (S : Finset V) (n : ℕ) :
    (propagate (reductionPull e H) S n).map e.toEmbedding =
      propagate H (S.map e.toEmbedding) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [propagate, reduction_step_transport, ih]

theorem reduction_obs_transport (e : V ≃ W) (H : SimpleGraph W)
    (S : Finset V) (n : ℕ) :
    (obs (reductionPull e H) S n).map e.toEmbedding = obs H (S.map e.toEmbedding) n := by
  cases n with
  | zero => rfl
  | succ n => simp only [obs, reduction_propagate_transport, reduction_closed_transport]

theorem reduction_isPD_transport (e : V ≃ W) (H : SimpleGraph W) (S : Finset V) :
    IsPD (reductionPull e H) S ↔ IsPD H (S.map e.toEmbedding) := by
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨n,?_⟩
    rw [← reduction_obs_transport,hn]
    simp
  · rintro ⟨n,hn⟩
    refine ⟨n,?_⟩
    apply (map_injective e.toEmbedding)
    rw [reduction_obs_transport,hn]
    simp

/-- A completed bridge: a PD-family equivalence suffices for the frozen reduction. -/
theorem reduction_of_family_equiv (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ≃ W) (hp : ∀ S, IsPD G S ↔ IsPD H (S.map e.toEmbedding)) :
    ∃ H' : SimpleGraph V, Nonempty (H ≃g H') ∧ SamePD G H' := by
  refine ⟨reductionPull e H, ⟨(SimpleGraph.Iso.comap e H).symm⟩,?_⟩
  intro S
  exact (hp S).trans (reduction_isPD_transport e H S).symm
end PDTAR
