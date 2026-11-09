import PDTAR.SmallTwoFamily
import PDTAR.ReductionTransport
namespace PDTAR
open Finset

def small_two_added (t : ℕ) : SimpleGraph (Fin 2 ⊕ Fin t) where
  Adj x y := match x,y with
    | Sum.inl a, Sum.inl b => a ≠ b
    | Sum.inr _, Sum.inr _ => False
    | _,_ => True
  symm := ⟨by intro x y; cases x <;> cases y <;> simp_all [ne_comm]⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

theorem small_bipartite_no_triangle {A B : Type}
    (x y z : A ⊕ B)
    (hxy : (completeBipartiteGraph A B).Adj x y)
    (hyz : (completeBipartiteGraph A B).Adj y z) :
    ¬ (completeBipartiteGraph A B).Adj z x := by
  cases x <;> cases y <;> cases z <;> simp_all [completeBipartiteGraph]

theorem small_two_witness (t : ℕ) (ht : 1 ≤ t) :
    ∃ H : SimpleGraph (Fin 2 ⊕ Fin t), NoIsolated H ∧
      SamePD (completeBipartiteGraph (Fin 2) (Fin t)) H ∧
      ¬ Nonempty (H ≃g completeBipartiteGraph (Fin 2) (Fin t)) := by
  let H := small_two_added t
  have hc : ∀ a b, H.Adj (Sum.inl a) (Sum.inr b) := by intros; trivial
  have hr : ∀ b c, ¬ H.Adj (Sum.inr b) (Sum.inr c) := by intros; exact id
  refine ⟨H,?_,?_,?_⟩
  · intro v
    cases v with
    | inl a => exact ⟨Sum.inr ⟨0,by omega⟩,hc _ _⟩
    | inr b => exact ⟨Sum.inl 0,(hc _ _).symm⟩
  · intro S
    exact (small_two_family t ht _ (by intros; simp [completeBipartiteGraph])
      (by intros; simp [completeBipartiteGraph]) S).trans
      (small_two_family t ht H hc hr S).symm
  · rintro ⟨e⟩
    have hab : H.Adj (Sum.inl 0) (Sum.inl 1) := by change (0 : Fin 2) ≠ 1; decide
    have hbc := hc 1 ⟨0,by omega⟩
    have hca := (hc 0 ⟨0,by omega⟩).symm
    exact small_bipartite_no_triangle _ _ _ (e.map_rel_iff.mpr hab)
      (e.map_rel_iff.mpr hbc) (e.map_rel_iff.mpr hca)

theorem small_witness_swap (s t : ℕ)
    (hw : ∃ H : SimpleGraph (Fin s ⊕ Fin t), NoIsolated H ∧
      SamePD (completeBipartiteGraph (Fin s) (Fin t)) H ∧
      ¬ Nonempty (H ≃g completeBipartiteGraph (Fin s) (Fin t))) :
    ∃ H : SimpleGraph (Fin t ⊕ Fin s), NoIsolated H ∧
      SamePD (completeBipartiteGraph (Fin t) (Fin s)) H ∧
      ¬ Nonempty (H ≃g completeBipartiteGraph (Fin t) (Fin s)) := by
  obtain ⟨H,hH,he,hn⟩ := hw
  let e : (Fin t ⊕ Fin s) ≃ (Fin s ⊕ Fin t) := Equiv.sumComm _ _
  let K := completeBipartiteGraph (Fin s) (Fin t)
  have hK : reductionPull e K = completeBipartiteGraph (Fin t) (Fin s) := by
    ext x y
    cases x <;> cases y <;> simp [reductionPull,K,e,completeBipartiteGraph]
  refine ⟨reductionPull e H,noIsolated_iso hH (SimpleGraph.Iso.comap e H).symm,?_,?_⟩
  · intro S
    rw [← hK]
    exact (reduction_isPD_transport e K S).trans
      ((he _).trans (reduction_isPD_transport e H S).symm)
  · rintro ⟨f⟩
    rw [← hK] at f
    exact hn ⟨(SimpleGraph.Iso.comap e H).symm.trans
      (f.trans (SimpleGraph.Iso.comap e K))⟩

theorem twoWitnessRemaining : TwoWitnessRemaining := by
  intro s t hs ht htwo
  rcases htwo with rfl | rfl
  · exact small_two_witness t ht
  · exact small_witness_swap 2 s (small_two_witness s hs)
end PDTAR
