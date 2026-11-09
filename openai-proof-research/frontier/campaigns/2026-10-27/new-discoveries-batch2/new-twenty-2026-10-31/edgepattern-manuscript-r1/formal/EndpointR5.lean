import HomR5
import BridgeR3
namespace EdgePattern.TreeModelsR5
open TreeModelsR3
set_option linter.unusedSimpArgs false
universe u

theorem pattern_connected (k : Counts) : (graph k).Connected := by
  have hr (x : V k) : (graph k).Reachable x (pattern k).left := by
    have h := distance_eq k x
    change min ((graph k).edist x (pattern k).left)
      ((graph k).edist x (pattern k).right) = (level x : ℕ∞) at h
    have hm : min ((graph k).edist x (pattern k).left)
      ((graph k).edist x (pattern k).right) ≠ ⊤ := by rw [h]; simp
    by_cases hl : (graph k).edist x (pattern k).left = ⊤
    · have he : (graph k).edist x (pattern k).right ≠ ⊤ := by simpa [hl] using hm
      exact (SimpleGraph.reachable_of_edist_ne_top he).trans (pattern k).root_edge.symm.reachable
    · exact SimpleGraph.reachable_of_edist_ne_top hl
  let : Nonempty (V k) := ⟨(pattern k).left⟩
  exact ⟨fun x y => (hr x).trans (hr y).symm⟩

variable {W : Type u} [Fintype W] (T : Rooted W)
noncomputable def modelHom (B : Branches T) (hT : TreeFamily T 3 2) :
    graph (branchCounts T B hT) →g T.graph where
  toFun := vertexEquiv T B hT
  map_rel' := by
    intro x y h
    obtain ⟨s,rfl⟩ := (number T B hT).surjective x
    obtain ⟨t,rfl⟩ := (number T B hT).surjective y
    change T.graph.Adj
      (slotValue T B ((number T B hT).symm (number T B hT s)))
      (slotValue T B ((number T B hT).symm (number T B hT t)))
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases h with h | h
    · exact forward_slots T B hT s t h
    · exact (forward_slots T B hT t s h).symm

noncomputable def modelIso (B : Branches T) (hT : TreeFamily T 3 2) :
    graph (branchCounts T B hT) ≃g T.graph where
  toEquiv := vertexEquiv T B hT
  map_rel_iff' := by
    intro x y
    constructor
    · exact reflects_adjacency (modelHom T B hT) (vertexEquiv T B hT).injective
        (pattern_connected _) hT.2
    · exact (modelHom T B hT).map_adj

-- Root labels are fixed by the first two slots of the numbering.
theorem vertexEquiv_left (B : Branches T) (hT : TreeFamily T 3 2) :
    vertexEquiv T B hT (pattern (branchCounts T B hT)).left = T.left := by
  have hn : number T B hT (.inl 0) = (pattern (branchCounts T B hT)).left := by
    apply Fin.ext
    rfl
  rw [← hn]
  change slotValue T B ((number T B hT).symm (number T B hT (.inl 0))) = _
  simp [slotValue]

theorem vertexEquiv_right (B : Branches T) (hT : TreeFamily T 3 2) :
    vertexEquiv T B hT (pattern (branchCounts T B hT)).right = T.right := by
  have hn : number T B hT (.inl 1) = (pattern (branchCounts T B hT)).right := by
    apply Fin.ext
    rfl
  rw [← hn]
  change slotValue T B ((number T B hT).symm (number T B hT (.inl 1))) = _
  simp [slotValue]

theorem classification : ClassifiedCubicTrees := by
  intro W _ T hT
  obtain ⟨B⟩ := branches_exist T hT
  refine ⟨branchCounts T B hT,⟨⟨(modelIso T B hT).symm,?_,?_⟩⟩⟩
  · change (vertexEquiv T B hT).symm T.left = _
    apply (vertexEquiv T B hT).injective
    rw [Equiv.apply_symm_apply]
    exact (vertexEquiv_left T B hT).symm
  · change (vertexEquiv T B hT).symm T.right = _
    apply (vertexEquiv T B hT).injective
    rw [Equiv.apply_symm_apply]
    exact (vertexEquiv_right T B hT).symm

theorem refutation : ¬ EdgePattern.Conjecture2.{0} :=
  neg_conjecture_of_classification classification
#print axioms classification
#print axioms refutation
end EdgePattern.TreeModelsR5
