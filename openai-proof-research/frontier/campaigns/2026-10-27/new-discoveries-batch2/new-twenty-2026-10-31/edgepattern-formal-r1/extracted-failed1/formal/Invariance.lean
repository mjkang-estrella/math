import Definitions
namespace EdgePattern
universe u v
variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W]
  {G : SimpleGraph V} {H : SimpleGraph W}

structure RootedIso (P : Rooted V) (Q : Rooted W) where
  iso : P.graph ≃g Q.graph
  left_eq : iso P.left = Q.left
  right_eq : iso P.right = Q.right

theorem independent_map_iff (e : G ≃g H) (s : Finset V) :
    Independent H (s.map e.toEquiv.toEmbedding) ↔ Independent G s := by
  simp only [Independent, Finset.forall_mem_map]
  change (∀ x ∈ s, ∀ y ∈ s, ¬ H.Adj (e x) (e y)) ↔ _
  simp only [e.map_adj_iff]

theorem maximum_map_iff (e : G ≃g H) (s : Finset V) :
    Maximum H (s.map e.toEquiv.toEmbedding) ↔ Maximum G s := by
  constructor
  · intro h
    refine ⟨(independent_map_iff e s).mp h.1, ?_⟩
    intro t ht
    have hb := h.2 (t.map e.toEquiv.toEmbedding) ((independent_map_iff e t).mpr ht)
    simpa using hb
  · intro h
    refine ⟨(independent_map_iff e s).mpr h.1, ?_⟩
    intro t ht
    have hb := h.2 (t.map e.symm.toEquiv.toEmbedding) ((independent_map_iff e.symm t).mpr ht)
    simpa using hb
end EdgePattern
