import StarMinimum
set_option autoImplicit false
namespace SteinerReflection
open SimpleGraph
noncomputable section
open Finset
abbrev star := starGraph (0:V)
def liftSubgraph (E : Finset V) (S : (edgeGraph E).Subgraph) : star.Subgraph where
  verts := S.verts
  Adj := S.Adj
  adj_sub h := edgeGraph_le E (S.adj_sub h)
  edge_vert h := S.edge_vert h
  symm := S.symm
lemma lift_connected (E : Finset V) (S : (edgeGraph E).Subgraph) (hc : S.Connected) :
    (liftSubgraph E S).Connected := ⟨hc.coe⟩
noncomputable def component (t : Fin 4 → V) : star.Subgraph :=
  liftSubgraph (required t) (((edgeGraph (required t)).connectedComponentMk (t 0)).toSubgraph)
noncomputable def edgeLabels (S : star.Subgraph) : Finset V := by
  classical
  exact leaves.filter fun j => S.Adj 0 j
lemma labels_mem (S : star.Subgraph) (j : V) :
    j ∈ edgeLabels S ↔ j ≠ 0 ∧ S.Adj 0 j := by
  classical
  simp [edgeLabels,leaves]
lemma component_connected (t : Fin 4 → V) : (component t).Connected :=
  lift_connected _ _ (ConnectedComponent.connected_toSubgraph _)
lemma component_contains (t : Fin 4 → V) (a : Fin 4) : t a ∈ (component t).verts := by
  change (edgeGraph (required t)).connectedComponentMk (t a) =
    (edgeGraph (required t)).connectedComponentMk (t 0)
  exact ConnectedComponent.sound ((required_feasible t).2 a 0)
lemma component_labels (t : Fin 4 → V) : edgeLabels (component t) = required t := by
  classical
  ext j
  rw [labels_mem]
  constructor
  · intro h
    have hg : (edgeGraph (required t)).Adj 0 j := h.2.2.2
    exact hg.2.elim (fun h => h.2) (fun h => (h.1.symm ▸ h.2))
  · intro hj
    have hz := (required_mem t j).mp hj
    obtain ⟨a,ha⟩ := hz.2.1
    have hadj : (edgeGraph (required t)).Adj 0 j := ⟨Ne.symm hz.1,Or.inl ⟨rfl,hj⟩⟩
    have hrj := (required_feasible t).2 0 a
    rw [ha] at hrj
    have hr0 := hrj.trans hadj.reachable.symm
    refine ⟨hz.1,?_,?_,hadj⟩
    · exact ConnectedComponent.sound hr0.symm
    · exact ConnectedComponent.sound hrj.symm
lemma labels_feasible (t : Fin 4 → V) (S : star.Subgraph) (hc : S.Connected)
    (ht : ∀ a, t a ∈ S.verts) : Feasible t (edgeLabels S) := by
  classical
  refine ⟨Finset.filter_subset _ _,fun a b => ?_⟩
  let f : S.coe →g edgeGraph (edgeLabels S) := {
    toFun := fun v => v.val
    map_rel' := by
      intro u v huv
      have hstar := starGraph_adj.mp (S.adj_sub huv)
      refine ⟨hstar.1,?_⟩
      rcases hstar.2 with hu | hv
      · exact Or.inl ⟨hu,(labels_mem S v).mpr ⟨by simpa [hu] using Ne.symm hstar.1,hu ▸ huv⟩⟩
      · exact Or.inr ⟨hv,(labels_mem S u).mpr ⟨by simpa [hv] using hstar.1,hv ▸ S.symm.symm _ _ huv⟩⟩ }
  exact (hc ⟨t a,ht a⟩ ⟨t b,ht b⟩).map f
/-- Size uses the bijective labels j ↔ {0,j} of all possible star edges. -/
def SubgraphSize (S : star.Subgraph) : ℕ := (edgeLabels S).card
/-- The labeling counts actual undirected edges exactly once. -/
lemma SubgraphSize_eq_edge_ncard (S : star.Subgraph) : SubgraphSize S = S.edgeSet.ncard := by
  classical
  have hb : Set.BijOn (fun j : V => s((0:V),j)) (↑(edgeLabels S) : Set V) S.edgeSet := by
    refine ⟨?_,?_,?_⟩
    · intro j hj; exact ((labels_mem S j).mp hj).2
    · intro j hj k hk he
      have he' : j = k ∨ (0:V) = k ∧ j = 0 := by simpa using he
      exact he'.elim id (fun h => h.2.trans h.1)
    · intro e he
      induction e using Sym2.inductionOn with | hf u v
      have hadj : S.Adj u v := he
      have hs := SimpleGraph.starGraph_adj.mp (S.adj_sub hadj)
      rcases hs.2 with hu | hv
      · subst u
        exact ⟨v,(labels_mem S v).mpr ⟨Ne.symm hs.1,hadj⟩,rfl⟩
      · subst v
        exact ⟨u,(labels_mem S u).mpr ⟨hs.1,S.symm.symm _ _ hadj⟩,Sym2.eq_swap⟩
  simpa [SubgraphSize] using hb.ncard_eq
lemma source_nonempty (t : Fin 4 → V) : ∃ n : ℕ, ∃ S : star.Subgraph,
    S.Connected ∧ (∀ a, t a ∈ S.verts) ∧ SubgraphSize S = n :=
  ⟨_,component t,component_connected t,component_contains t,rfl⟩
/-- Minimum edge count of a connected subgraph containing every ordered terminal, repetitions allowed. -/
def sourceDistance (t : Fin 4 → V) : ℕ := by
  classical
  exact Nat.find (source_nonempty t)
theorem sourceDistance_eq (t : Fin 4 → V) : sourceDistance t = minimumDistance t := by
  classical
  apply Nat.le_antisymm
  · change Nat.find (source_nonempty t) ≤ _
    apply Nat.find_min'
    refine ⟨component t,component_connected t,component_contains t,?_⟩
    simp only [SubgraphSize,component_labels,minimumDistance_eq]
  · obtain ⟨S,hc,ht,hn⟩ := Nat.find_spec (source_nonempty t)
    change minimumDistance t ≤ Nat.find (source_nonempty t)
    rw [←hn,minimumDistance_eq]
    exact Finset.card_le_card (required_subset t _ (labels_feasible t S hc ht))
theorem source_minimum_attained (t : Fin 4 → V) : ∃ S : star.Subgraph,
    S.Connected ∧ (∀ a, t a ∈ S.verts) ∧ S.edgeSet.ncard = sourceDistance t ∧
    ∀ F : star.Subgraph, F.Connected → (∀ a, t a ∈ F.verts) →
      S.edgeSet.ncard ≤ F.edgeSet.ncard := by
  classical
  refine ⟨component t,component_connected t,component_contains t,?_,?_⟩
  · rw [←SubgraphSize_eq_edge_ncard,SubgraphSize,component_labels,
      sourceDistance_eq,minimumDistance_eq]
  · intro F hc ht
    rw [←SubgraphSize_eq_edge_ncard,←SubgraphSize_eq_edge_ncard]
    simp only [SubgraphSize,component_labels]
    exact Finset.card_le_card (required_subset t _ (labels_feasible t F hc ht))
end
end SteinerReflection
