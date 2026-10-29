import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Real.Archimedean
set_option autoImplicit false
set_option warningAsError true
namespace EdgeIrregulator
open SimpleGraph
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]
def Retained (G : SimpleGraph V) (S : Finset (Sym2 V)) : SimpleGraph V :=
  G.deleteEdges (S : Set (Sym2 V))
def Valid (G : SimpleGraph V) (S : Finset (Sym2 V)) : Prop :=
  S ⊆ G.edgeFinset ∧ ∀ u v, (Retained G S).Adj u v →
    (Retained G S).degree u ≠ (Retained G S).degree v
 theorem valid_delete_all (G : SimpleGraph V) : Valid G G.edgeFinset := by
  classical
  constructor
  · exact Finset.Subset.refl _
  · intro u v h
    have h' := h
    simp [Retained, SimpleGraph.deleteEdges_adj] at h'
 theorem exists_valid (G : SimpleGraph V) : ∃ k : ℕ, ∃ S, Valid G S ∧ S.card = k :=
  ⟨G.edgeFinset.card, G.edgeFinset, valid_delete_all G, rfl⟩
def minimum (G : SimpleGraph V) : ℕ := Nat.find (exists_valid G)
 theorem minimum_attained (G : SimpleGraph V) : ∃ S, Valid G S ∧ S.card = minimum G :=
  Nat.find_spec (exists_valid G)
 theorem minimum_le (G : SimpleGraph V) (S : Finset (Sym2 V)) (h : Valid G S) :
    minimum G ≤ S.card := Nat.find_min' (exists_valid G) ⟨S, h, rfl⟩
 theorem minimum_le_iff (G : SimpleGraph V) (b : ℝ) :
    (minimum G : ℝ) ≤ b ↔ ∃ S, Valid G S ∧ (S.card : ℝ) ≤ b := by
  constructor
  · intro h
    obtain ⟨S,hS,hc⟩ := minimum_attained G
    exact ⟨S,hS,by simpa [hc] using h⟩
  · rintro ⟨S,hS,hc⟩
    exact le_trans (by exact_mod_cast minimum_le G S hS) hc
-- All Fin n graphs are a literal finite simple graph source model.
def SourceClaim : Prop := ∃ c : ℝ, 1 ≤ c ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  G.Connected → ∃ S, Valid G S ∧ (S.card : ℝ) ≤ (G.edgeFinset.card : ℝ)/3+c
def MinimumSourceClaim : Prop := ∃ c : ℝ, 1 ≤ c ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  G.Connected → (minimum G : ℝ) ≤ (G.edgeFinset.card : ℝ)/3+c
 theorem source_minimum_equivalence : SourceClaim ↔ MinimumSourceClaim := by
  simp only [SourceClaim, MinimumSourceClaim, minimum_le_iff]
end
end EdgeIrregulator
