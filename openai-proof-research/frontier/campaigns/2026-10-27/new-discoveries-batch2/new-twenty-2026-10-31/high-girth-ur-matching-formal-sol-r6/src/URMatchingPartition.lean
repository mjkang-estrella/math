module
public import URMatchingBase
@[expose] public section
namespace URMatching
universe v
variable {V : Type v}
/-- The bipartition is an actual proper two-coloring of every graph edge. -/
def AcrossPartition (G : SimpleGraph V) (P : V → Prop) : Prop :=
  ∀ x y, G.Adj x y → (P x ↔ ¬ P y)

theorem partition_orients_edge (G : SimpleGraph V) (P : V → Prop)
    (bip : AcrossPartition G P) (a : Sym2 V) (he : a ∈ G.edgeSet) :
    ∃ x y, P x ∧ ¬ P y ∧ a = s(x,y) := by
  classical
  revert he
  refine Sym2.inductionOn a (fun x y hxy => ?_)
  have hadj : G.Adj x y := hxy
  by_cases hp : P x
  · exact ⟨x, y, hp, (bip x y hadj).mp hp, rfl⟩
  · have hpy : P y := by
      by_contra hny
      exact hp ((bip x y hadj).mpr hny)
    exact ⟨y, x, hpy, hp, by simp [Sym2.eq_swap]⟩
end URMatching
