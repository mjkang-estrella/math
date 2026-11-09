import SupportGraph
import Mathlib.Logic.Equiv.Fin.Basic
namespace Nut8
attribute [local instance] Classical.propDecidable
/-- Delete a vertex and retain the standard finite vertex type. -/
def deleteFin {n : ℕ} (G : SimpleGraph (Fin (n+1))) (v : Fin (n+1)) :
    SimpleGraph (Fin n) := G.comap v.succAbove

/-- The finite deletion agrees with the induced complement, including its labels. -/
def deleteFinIso {n : ℕ} (G : SimpleGraph (Fin (n+1))) (v : Fin (n+1)) :
    deleteFin G v ≃g G.induce {v}ᶜ where
  toEquiv := finSuccAboveEquiv v
  map_rel_iff' := by intros; rfl

theorem deleteFin_degree_le {n : ℕ} (G : SimpleGraph (Fin (n+1)))
    (v : Fin (n+1)) (i : Fin n) :
    (deleteFin G v).degree i ≤ G.degree (v.succAbove i) := by
  classical
  let f : (deleteFin G v).neighborSet i → G.neighborSet (v.succAbove i) :=
    fun j => ⟨v.succAbove j.val, j.property⟩
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    exact v.succAbove_right_injective (congrArg Subtype.val he)
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using Fintype.card_le_of_injective f hf

theorem connected_deleteFin (k : ℕ) (G : SimpleGraph (Fin (k+2)))
    (h : G.Connected) : ∃ v, (deleteFin G v).Connected := by
  obtain ⟨v, hv⟩ := connected_removable_vertex k G h
  exact ⟨v, (deleteFinIso G v).connected_iff.mpr hv⟩

/-- The deletion step preserves both hypotheses needed by catalogue induction. -/
theorem connected_subcubic_deleteFin (k : ℕ) (G : SimpleGraph (Fin (k+2)))
    (h : G.Connected) (hd : ∀ i, G.degree i ≤ 3) :
    ∃ v, (deleteFin G v).Connected ∧ ∀ i, (deleteFin G v).degree i ≤ 3 := by
  obtain ⟨v, hv⟩ := connected_deleteFin k G h
  exact ⟨v, hv, fun i => (deleteFin_degree_le G v i).trans (hd _)⟩
end Nut8
